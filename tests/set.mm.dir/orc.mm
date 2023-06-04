include "pm2.24.mm";
include "orrd.mm";

theorem orc(wph: 'wff' ph, wps: 'wff' ps) {





  do {
    wph;
    wph;
    wps;
    wph;
    wps;
    pm2.24;
    orrd;
  };

  return '|-' "( ph -> ( ph \\/ ps ) )";
}
