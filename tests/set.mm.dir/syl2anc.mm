include "ex.mm";
include "sylc.mm";

theorem syl2anc(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th) {
  assume syl2anc.1: |- "( ph -> ps )";
  assume syl2anc.2: |- "( ph -> ch )";
  assume syl2anc.3: |- "( ( ps /\\ ch ) -> th )";





  do {
    wph;
    wps;
    wch;
    wth;
    syl2anc.1;
    syl2anc.2;
    wps;
    wch;
    wth;
    syl2anc.3;
    ex;
    sylc;
  };

  return |- "( ph -> th )";
}
