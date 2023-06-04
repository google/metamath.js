include "wi.mm";
include "wn.mm";
include "wo.mm";
include "notnotb.mm";
include "imbi1i.mm";
include "df-or.mm";
include "bitr4i.mm";

theorem imor(wph: 'wff' ph, wps: 'wff' ps) {





  do {
    wph;
    wps;
    wi;
    wph;
    wn;
    #;
    wn;
    #;
    wps;
    wi;
    @0;
    wps;
    wo;
    wph;
    @1;
    wps;
    wph;
    notnotb;
    imbi1i;
    @0;
    wps;
    df-or;
    bitr4i;
  };

  return '|-' "( ( ph -> ps ) <-> ( -. ph \\/ ps ) )";
}
