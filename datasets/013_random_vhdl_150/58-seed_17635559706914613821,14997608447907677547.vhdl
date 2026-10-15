-- Seed: 17635559706914613821,14997608447907677547



entity qhnqeizw is
  port (hhjwsnb : out time);
end qhnqeizw;



architecture m of qhnqeizw is
  
begin
  
end m;



entity tgr is
  port (x : buffer real; uwzzrxzlz : out boolean);
end tgr;



architecture xmgr of tgr is
  signal ixzkjybb : time;
begin
  qmptpgfg : entity work.qhnqeizw
    port map (hhjwsnb => ixzkjybb);
end xmgr;



entity gumjvhco is
  port (btzl : buffer integer; db : in time);
end gumjvhco;



architecture gbncxi of gumjvhco is
  signal lmilagvuxt : time;
  signal dwaxcdxw : time;
  signal wnfwdrnbq : time;
  signal cbhtx : time;
begin
  zol : entity work.qhnqeizw
    port map (hhjwsnb => cbhtx);
  szoe : entity work.qhnqeizw
    port map (hhjwsnb => wnfwdrnbq);
  mrvhedqhf : entity work.qhnqeizw
    port map (hhjwsnb => dwaxcdxw);
  n : entity work.qhnqeizw
    port map (hhjwsnb => lmilagvuxt);
end gbncxi;



-- Seed after: 12242914696244132710,14997608447907677547
