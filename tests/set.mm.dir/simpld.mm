include "wa.mm";
include "simpl.mm";
include "syl.mm";

theorem simpld(wph: wff ph, wps: wff ps, wch: wff ch) {
  assume simpld.1: |- "( ph -> ( ps /\\ ch ) )";





  do {
    wph;
    wps;
    wch;
    wa;
    wps;
    simpld.1;
    wps;
    wch;
    simpl;
    syl;
  };

  return |- "( ph -> ps )";
}
