include "wn.mm";
include "wi.mm";
include "con1.mm";
include "impbii.mm";

theorem con1b(wph: wff ph, wps: wff ps) {





  do {
    wph;
    wn;
    wps;
    wi;
    wps;
    wn;
    wph;
    wi;
    wph;
    wps;
    con1;
    wps;
    wph;
    con1;
    impbii;
  };

  return |- "( ( -. ph -> ps ) <-> ( -. ps -> ph ) )";
}
