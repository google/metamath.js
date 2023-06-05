include "wo.mm";
include "orc.mm";
include "imim1i.mm";

theorem pm2.67-2(wph: wff ph, wps: wff ps, wch: wff ch) {





  do {
    wph;
    wph;
    wch;
    wo;
    wps;
    wph;
    wch;
    orc;
    imim1i;
  };

  return |- "( ( ( ph \\/ ch ) -> ps ) -> ( ph -> ps ) )";
}
