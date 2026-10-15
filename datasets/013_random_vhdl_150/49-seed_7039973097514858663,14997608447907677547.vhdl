-- Seed: 7039973097514858663,14997608447907677547

library ieee;
use ieee.std_logic_1164.all;

entity wdsjmhieh is
  port (brww : inout std_logic; cbyznun : buffer time; o : linkage std_logic; vld : buffer integer);
end wdsjmhieh;



architecture xoy of wdsjmhieh is
  
begin
  
end xoy;

library ieee;
use ieee.std_logic_1164.all;

entity k is
  port (qea : out std_logic; uhsm : buffer std_logic; mjyrf : out real; kxt : in integer);
end k;

library ieee;
use ieee.std_logic_1164.all;

architecture taiffyre of k is
  signal bn : integer;
  signal gdfrbnwp : time;
  signal rxlfzbbzfv : std_logic;
  signal jrkdmtehd : integer;
  signal mookg : std_logic;
  signal swnjul : time;
  signal dsvrt : integer;
  signal qju : time;
begin
  spp : entity work.wdsjmhieh
    port map (brww => qea, cbyznun => qju, o => uhsm, vld => dsvrt);
  j : entity work.wdsjmhieh
    port map (brww => uhsm, cbyznun => swnjul, o => mookg, vld => jrkdmtehd);
  nrzdwdty : entity work.wdsjmhieh
    port map (brww => rxlfzbbzfv, cbyznun => gdfrbnwp, o => mookg, vld => bn);
end taiffyre;

library ieee;
use ieee.std_logic_1164.all;

entity qyiybv is
  port (xsul : out integer; kmozm : out time; fosoass : linkage std_logic);
end qyiybv;

library ieee;
use ieee.std_logic_1164.all;

architecture gcitwgc of qyiybv is
  signal elbcvryv : integer;
  signal lsyto : integer;
  signal gm : time;
  signal mnb : std_logic;
  signal hxg : time;
  signal ozecc : std_logic;
begin
  oyfb : entity work.wdsjmhieh
    port map (brww => ozecc, cbyznun => hxg, o => fosoass, vld => xsul);
  l : entity work.wdsjmhieh
    port map (brww => mnb, cbyznun => gm, o => fosoass, vld => lsyto);
  lqgzx : entity work.wdsjmhieh
    port map (brww => ozecc, cbyznun => kmozm, o => fosoass, vld => elbcvryv);
end gcitwgc;

library ieee;
use ieee.std_logic_1164.all;

entity hjcnqu is
  port (iusltqa : buffer character; kgcytexc : buffer std_logic);
end hjcnqu;

library ieee;
use ieee.std_logic_1164.all;

architecture ngixr of hjcnqu is
  signal ek : std_logic;
  signal w : time;
  signal chnknhbjfr : std_logic;
  signal kv : integer;
  signal dsxau : real;
  signal xd : integer;
  signal dwpyjffaze : time;
  signal xjhubn : std_logic;
  signal bce : time;
  signal ovvrjpq : integer;
begin
  fdzvsa : entity work.qyiybv
    port map (xsul => ovvrjpq, kmozm => bce, fosoass => kgcytexc);
  djrihwc : entity work.wdsjmhieh
    port map (brww => xjhubn, cbyznun => dwpyjffaze, o => kgcytexc, vld => xd);
  ljzf : entity work.k
    port map (qea => kgcytexc, uhsm => kgcytexc, mjyrf => dsxau, kxt => kv);
  sasehs : entity work.wdsjmhieh
    port map (brww => chnknhbjfr, cbyznun => w, o => ek, vld => kv);
end ngixr;



-- Seed after: 6869025727829000401,14997608447907677547
