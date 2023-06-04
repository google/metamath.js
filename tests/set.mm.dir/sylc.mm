include "syl2im.mm";
include "pm2.43i.mm";

theorem sylc(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, wth: 'wff' th) {
  assume sylc.1: |- "( ph -> ps )";
  assume sylc.2: |- "( ph -> ch )";
  assume sylc.3: |- "( ps -> ( ch -> th ) )";





  do {
    wph;
    wth;
    wph;
    wps;
    wph;
    wch;
    wth;
    sylc.1;
    sylc.2;
    sylc.3;
    syl2im;
    pm2.43i;
  };

  return '|-' "( ph -> th )";
}
