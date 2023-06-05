include "wa.mm";
include "id.mm";
include "ex.mm";

theorem pm3.2(wph: wff ph, wps: wff ps) {





  do {
    wph;
    wps;
    wph;
    wps;
    wa;
    #;
    @0;
    id;
    ex;
  };

  return |- "( ph -> ( ps -> ( ph /\\ ps ) ) )";
}
