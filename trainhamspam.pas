program trainhamspam;

{==============================================================================

Programa arrancado desde notifyd (siempre que se haya configurado) para gestionar
eventos.
El evento se envía en formato json a standard input, ver
https://cyrusimap.org/imap/concepts/features/event-notifications.html

Solo gestiona los eventos MessageMove (vnd.cmu.MessageMove) y MessageCopy
(vnd.cmu.MessageCopy) para detectar
si se ha movido el mensaje de/a la carpeta spam personal 
Si el destino es spam se llama "rspamc learn_spam" si la procedencia
es spam se llama "rspamc learn_ham".

Para evitar ocupar notifyd demasiado tiempo, rspamc se ejecuta en un nuevo
proceso y no se espera su fin.

Para que todo funcione, hay que configurar en /etc/imapd.conf

  event_notifier: external
  notifysocket: /var/run/cyrus/socket/notify
  notify_external: /usr/local/bin/trainhamspam

(o donde esté puesto el programa)

}
{$mode objfpc}{$H+}
{$modeswitch typehelpers}

uses
  {$IFDEF UNIX}{$IFDEF UseCThreads}
  cthreads,
  {$ENDIF}{$ENDIF}
  Classes, sysutils, fpjson, jsonparser,systemlog,BaseUnix,process, StreamIO;

type
  TMailbox = record
    user:string;
    mailbox:string;
    path:string;
  end;

  TStringHelper = Type Helper for AnsiString
  public
    Function StartsWith(const AValue: string): Boolean; overload; inline;
    Function StartsWith(const AValue: string; IgnoreCase: Boolean): Boolean; overload;
  end;

const
  //tal vez sea mejor ponerlos en un fichero de configuración
  SPOOL='/var/spool/cyrus/mail/'; //ubicación del spool
  SPAMFOLDER='spam';              //nombre de la carpeta spam personal
  TRASHFOLDER='Trash';            //nombre de la papelera
  SEPARATOR='.';                  //cambiar a '/' si se activa unixhierarchysep
  USERSNAMESPACE='user';          //donde están las carpetas de usuarios
  USERS=USERSNAMESPACE+SEPARATOR; //prefijo de las carpetas de usuario
  IMAPURI='imap://';
  INBOX='INBOX';

  //-----------------------------------------------------------------------------
  function TStringHelper.StartsWith(const AValue: string): Boolean;
  begin
    Result:=StartsWith(AValue,False);
  end;


  function TStringHelper.StartsWith(const AValue: string; IgnoreCase: Boolean
    ): Boolean;
  Var
    L : SizeInt;
    S : String;
    
  begin
    L:=System.Length(AValue);
    Result:=L<=0;
    if not Result then
      begin
      S:=System.Copy(Self,1,L);
      Result:=(System.Length(S)=L);
      if Result then
        if IgnoreCase then
          Result:=SameText(S,aValue)
        else
          Result:=CompareStr(S,AValue)=0;
      end;  
  end;

  
  //-----------------------------------------------------------------------------

  function HexChar(const c:char):byte;
  begin
    if (c>='0') and (c<='9') then
      result:=ord(c)-ord('0')
    else if (c>='A') and (c<='F') then
      result:=ord(c)-ord('A')+10
    else if (c>='a') and (c<='f') then
      result:=ord(c)-ord('a')+10
    else
      result:=0;
  end;

  {-----------------------------------------------------------------------------

    En el uri que viene en el mensaje, los caracteres especiales están urlencoded,
    además cyrus usa como nombre de directorio un uft7 modificado codificado en
    base64 para los caracteres especiales.
    Esta función descodifica los caracteres especiales y convierte a ese utf7
    extraño.

    adaptado de imapurl.c de cyrus
  }

  function URLtoMailbox(const src:string):string;
  const
    base64chars='ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+,';

    UTF16MASK=$3FF;
    UTF16SHIFT=10;
    UTF16BASE=$10000;
    UTF16HIGHSTART=$D800;
    //UTF16HIGHEND=$DBFF;
    UTF16LOSTART=$DC00;

  var utf8pos, utf8total,
      bitstogo, i, lsrc:integer;
      utf7mode, utf16flag:boolean;
      ucs4,bitbuf:dword;
      c:char;

    procedure EndUtf7;
    begin
      if (utf7mode) then
      begin
          if (bitstogo>0) then
              result:=result+base64chars[((bitbuf shl (6 - bitstogo)) AND $3F)+1];
          result:=result+'-';
          utf7mode := false;
          bitstogo := 0;
          bitbuf := 0;
      end;
    end;

  begin
      utf8pos:=0;
      ucs4:=0;
      bitbuf:=0;
      utf7mode := false; // is the output UTF7 currently in base64 mode?
      utf8total := 0; { how many octets is the current input UTF-8 char;
                        0 == between characters }
      bitstogo := 0; { bits that need to be encoded into base64; if
                       bitstogo <> 0 then utf7mode is True }
      i:=1;
      result:='';
      lsrc:=length(src);
      while i<=lsrc do
      begin
         c:=src[i];
         inc(i);


          // undo hex-encoding
          if (c = '%') and (i+1<=lsrc) then
          begin
              c:=chr(HexChar(src[i])*16+HexChar(src[i+1]));
              inc(i,2);
          end;

          if c=SEPARATOR then
            c:='/';

          // normal character?
          if (c >= ' ') and  (c <= '~') then
          begin
              // switch out of UTF-7 mode
              EndUtf7;
              result:=result+c;
              ///* encode '&' as '&-' */
              if (c = '&') then
                  result:=result+'-';
              continue;
          end;

          // switch to UTF-7 mode
          if not utf7mode then
          begin
              result:=result+'&';
              utf7mode := true;
          end;


          // Encode US-ASCII characters as themselves
          if ord(c) < $80 then
          begin
              ucs4 := ord(c);
              utf8total := 1;
          end else if (utf8total>0) then
          begin
              // this is a subsequent octet of a multi-octet character

              // save UTF8 bits into UCS4
              ucs4 := (ucs4 shl 6) or (ord(c) and $3f);
              inc(utf8pos);
              if utf8pos < utf8total then
                  continue;
          end else
          begin
              // this is the first octet of a multi-octet character

              utf8pos := 1;
              if ord(c) < $E0  then
              begin
                  utf8total := 2;
                  ucs4 := ord(c) and $1F;
              end
              else if ord(c) < $F0 then
              begin
                  utf8total := 3;
                  ucs4 := ord(c) and $0F;
              end
              else
              begin
                  // NOTE: can't convert UTF8 sequences longer than 4
                  utf8total := 4;
                  ucs4 := ord(c) and $03;
              end;
              continue;
          end;

          // finished with UTF-8 character. make sure it isn't an
          //   overlong sequence. if it is, drop that character
          if  ((ucs4 < $80) and (utf8total > 1)) or
              ((ucs4 < $0800) and (utf8total > 2)) or
              ((ucs4 < $00010000) and (utf8total > 3)) or
              ((ucs4 < $00200000) and (utf8total > 4)) or
              ((ucs4 < $04000000) and (utf8total > 5)) or
              ((ucs4 < $80000000) and (utf8total > 6)) then
          begin
              utf8total := 0;
              continue;
          end;
          utf8total := 0;

          // loop to split ucs4 into two utf16 chars if necessary
          repeat
              if ucs4 >= UTF16BASE then
              begin
                  dec(ucs4,UTF16BASE);
                  bitbuf := (bitbuf shl 16) or ((ucs4 shr UTF16SHIFT)
                                             + UTF16HIGHSTART);
                  ucs4 := (ucs4 and UTF16MASK) + UTF16LOSTART;
                  utf16flag := true;
              end else
              begin
                  bitbuf := (bitbuf shl 16) or ucs4;
                  utf16flag := false;
              end;
              inc(bitstogo,16);
              // spew out base64
              while bitstogo >= 6 do
              begin
                  dec(bitstogo,6);
                  if bitstogo>0 then
                    result:=result+base64chars[((bitbuf shr bitstogo) and $3f)+1]
                  else
                    result:=result+base64chars[(bitbuf and $3f)+1];
              end
          until not utf16flag;
      end;

      // if in UTF-7 mode, finish in ASCII
      EndUtf7;
  end;

{-----------------------------------------------------------------------------
  Descodifica el nombre de la carpeta (solo para su visualización en el log)
}
function URLDecode(s: string): string;
var
  i,lengthsource, j: integer;
begin
  lengthsource := length(s);
  setlength(result,lengthsource);
  i:=1;
  j:=1;
  while (i<=lengthsource) do
    begin
      if s[i] <> '%' then
        result[j] := s[i]
      else if (s[i] = '%') and (i+2<=lengthsource) then
        try
          begin
            result[j] := Chr(HexChar(s[i+1])*16+HexChar(s[i+2]));
            i:=i+2;
          end;
        except
        end
      else
        result[j] := s[i];
      inc(i);
      inc(j);
    end;
  setlength(result,j-1);
end;

{-----------------------------------------------------------------------------

Desde el uri de una carpeta determina el usuario, el nombre de la carpeta y
el path.

El uri tiene el formato imap://servidor/carpeta.subcarpeta

}

function hashchar(const s:string):char;
begin
  result:=LowerCase(s)[1];
  if (result<'a') or (result>'z') then
    result:='q';
end;

function parsemb(const mb:string):TMailbox;
var
  p: integer;
  s: String;
begin
  result.user:='';
  result.mailbox:='';
  result.path:='';
  if not mb.StartsWith(IMAPURI) then
    exit;
  s:=copy(mb,length(IMAPURI)+1,length(mb));
  //quita ;UIDVALIDITY....
  p:=pos(';',s);
  if p>0 then
    s:=copy(s,1,p-1);
  //quita el servidor server
  p:=pos('/',s);
  if p<=0 then
    exit;
  s:=copy(s,p+1,length(s));

  if s.StartsWith(USERS) then
  begin
    s:=copy(s,length(USERS)+1,length(s));
    result.mailbox:=s;
    //mira si es una subcarpeta o el INBOX
    p:=pos(SEPARATOR,s);
    if p<=0 then
    begin
      result.user:=s;
      result.mailbox:=INBOX;
    end else
    begin
       result.user:=copy(s,1,p-1);
       result.mailbox:=copy(s,p+1,length(s));
    end;
    //hashimapspool
    
    // result.path:=SPOOL+hashchar(result.user)+'/'+USERSNAMESPACE+'/'+result.user+'/';
    // no hash
    result.path:=SPOOL+USERSNAMESPACE+'/'+result.user+'/';
    if result.mailbox<>INBOX then
       result.path:=result.path+URLtoMailbox(result.mailbox)+'/';
  end else 
  begin
    exit
  end;
  //descodifica para visualización
  result.mailbox:=URLDecode(result.mailbox);
end;

{-----------------------------------------------------------------------------
  Crea un fork del programa para arrancar rspamc
}
procedure retrain(const mbox:TMailbox; const uid:string);
const DSPAM_HEADER='X-DSPAM-Signature: ';
var
  pid: TPid;
  filename:string;
  spam: Boolean;
  rspamcresult:string;
begin
  pid:=fpfork();
  case pid of
    -1:
      begin
        //syslog(LOG_ERR,'fork failed',[]);
        halt;
      end;
    0: //child
      begin
        filename:=mbox.path+uid+'.';
        spam:=mbox.mailbox=SPAMFOLDER;
        syslog(LOG_INFO,'user %s, mailbox %s, retrain %s como %s',[pchar(mbox.user),pchar(mbox.mailbox),pchar(filename),pchar(BoolToStr(spam,'spam','ham'))]);
        if RunCommand('/usr/bin/rspamc',[BoolToStr(spam,'learn_spam','learn_ham'), filename],rspamcresult) then
          syslog(LOG_INFO,'rspamc output: %s',[pchar(rspamcresult)])
        else
          syslog(LOG_ERR,'error ejecutando rspamc',[]);
      end
    else   //parent
      begin
        //syslog(LOG_INFO,'parent',[]);
        exit;
      end
  end;
end;

//-----------------------------------------------------------------------------

procedure DoRun;
var
  jdata: TJSONData;
  jsonstring, s, uidset: String;
  jobject: TJSONObject;
  oldmb, newmb: TMailbox;
  event: TJSONStringType;
  uids:TStringList;
begin
  openlog('trainhamspam',LOG_PID,LOG_USER);
  jdata:=nil;
  try
    jsonstring:='';
    s:='';
    //lee el mensaje de stdin
    while not eof do
    begin
      readln(s);
      jsonstring:=jsonstring+s;
    end;
    //lo intenta descodificar como json
    jdata:=GetJSON(jsonstring);
    //cast para simplificar resto operaciones
    jobject:=TJSONObject(jdata);
    event:=jobject['event'].AsString;
    case event of
      'vnd.cmu.MessageMove','vnd.cmu.MessageCopy': begin
         oldmb:=parsemb(jobject['oldMailboxID'].AsString);
         newmb:=parsemb(jobject['uri'].AsString);
         if (newmb.mailbox=SPAMFOLDER) or ((oldmb.mailbox=SPAMFOLDER) and (newmb.mailbox<>TRASHFOLDER)) then
         begin
           //uidset puede ser una lista separada por ':', iteramos sobre la lista para procesar todos los mensajes
           uids:=TStringList.Create;
           uids.delimiter:=':';
           uids.delimitedtext:=jobject['uidset'].AsString;
           for uidset in uids do
             retrain(newmb,uidset);
           uids.free;
         end;
      end;
    else
     //syslog(LOG_INFO,'mensaje json %s no se gestiona',[Pchar(event)]);
    end;
  except
    on e:exception do
      syslog(LOG_ERR, '%s',[PChar(e.message)]);
  end;
  jdata.free;
end;

//-----------------------------------------------------------------------------
var testname:string;
    testmb:TMailbox;
begin
  if ParamStr(1)='test' then
  begin
     while true do
     begin
       readln(testname);
       testmb:=parsemb(testname);
       writeln('user ',testmb.user);
       writeln('mbox ',testmb.mailbox);
       writeln('path ',testmb.path);
     end;
  end else
    DoRun;
end.

