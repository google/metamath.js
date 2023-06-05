include "wn.mm";
include "pm2.18.mm";
include "jarli.mm";

theorem notnotr(wph: wff ph) {





  do {
    wph;
    wn;
    wph;
    wph;
    wph;
    pm2.18;
    jarli;
  };

  return |- "( -. -. ph -> ph )";
}
