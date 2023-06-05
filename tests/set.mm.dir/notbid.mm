include "wn.mm";
include "notnotb.mm";
include "3bitr3g.mm";
include "con4bid.mm";

theorem notbid(wph: wff ph, wps: wff ps, wch: wff ch) {
  assume notbid.1: |- "( ph -> ( ps <-> ch ) )";





  do {
    wph;
    wps;
    wn;
    #;
    wch;
    wn;
    #;
    wph;
    wps;
    wch;
    @0;
    wn;
    @1;
    wn;
    notbid.1;
    wps;
    notnotb;
    wch;
    notnotb;
    3bitr3g;
    con4bid;
  };

  return |- "( ph -> ( -. ps <-> -. ch ) )";
}
