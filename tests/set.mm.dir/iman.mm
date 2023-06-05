include "wi.mm";
include "wn.mm";
include "wa.mm";
include "notnotb.mm";
include "imbi2i.mm";
include "imnan.mm";
include "bitri.mm";

theorem iman(wph: wff ph, wps: wff ps) {





  do {
    wph;
    wps;
    wi;
    wph;
    wps;
    wn;
    #;
    wn;
    #;
    wi;
    wph;
    @0;
    wa;
    wn;
    wps;
    @1;
    wph;
    wps;
    notnotb;
    imbi2i;
    wph;
    @0;
    imnan;
    bitri;
  };

  return |- "( ( ph -> ps ) <-> -. ( ph /\\ -. ps ) )";
}
