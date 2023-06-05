include "wn.mm";
include "notnot.mm";
include "syl6.mm";
include "con4d.mm";

theorem con1d(wph: wff ph, wps: wff ps, wch: wff ch) {
  assume con1d.1: |- "( ph -> ( -. ps -> ch ) )";





  do {
    wph;
    wps;
    wch;
    wn;
    #;
    wph;
    wps;
    wn;
    wch;
    @0;
    wn;
    con1d.1;
    wch;
    notnot;
    syl6;
    con4d;
  };

  return |- "( ph -> ( -. ch -> ps ) )";
}
