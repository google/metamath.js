include "wo.mm";
include "pm1.4.mm";
include "impbii.mm";

theorem orcom(wph: 'wff' ph, wps: 'wff' ps) {





  do {
    wph;
    wps;
    wo;
    wps;
    wph;
    wo;
    wph;
    wps;
    pm1.4;
    wps;
    wph;
    pm1.4;
    impbii;
  };

  return '|-' "( ( ph \\/ ps ) <-> ( ps \\/ ph ) )";
}
