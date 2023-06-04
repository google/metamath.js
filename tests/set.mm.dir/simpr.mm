include "id.mm";
include "adantl.mm";

theorem simpr(wph: 'wff' ph, wps: 'wff' ps) {





  do {
    wps;
    wps;
    wph;
    wps;
    id;
    adantl;
  };

  return '|-' "( ( ph /\\ ps ) -> ps )";
}
