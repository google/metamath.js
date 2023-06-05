include "wi.mm";
include "id.mm";
include "a1i.mm";

theorem idd(wph: wff ph, wps: wff ps) {





  do {
    wps;
    wps;
    wi;
    wph;
    wps;
    id;
    a1i;
  };

  return |- "( ph -> ( ps -> ps ) )";
}
