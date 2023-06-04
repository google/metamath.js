include "wn.mm";
include "wo.mm";
include "wi.mm";
include "wa.mm";
include "exmid.mm";
include "a1bi.mm";
include "jaob.mm";
include "bitr2i.mm";

theorem pm4.83(wph: 'wff' ph, wps: 'wff' ps) {





  do {
    wps;
    wph;
    wph;
    wn;
    #;
    wo;
    #;
    wps;
    wi;
    wph;
    wps;
    wi;
    @0;
    wps;
    wi;
    wa;
    @1;
    wps;
    wph;
    exmid;
    a1bi;
    wph;
    wps;
    @0;
    jaob;
    bitr2i;
  };

  return '|-' "( ( ( ph -> ps ) /\\ ( -. ph -> ps ) ) <-> ps )";
}
