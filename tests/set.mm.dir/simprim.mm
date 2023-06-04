include "idd.mm";
include "impi.mm";

theorem simprim(wph: 'wff' ph, wps: 'wff' ps) {





  do {
    wph;
    wps;
    wps;
    wph;
    wps;
    idd;
    impi;
  };

  return '|-' "( -. ( ph -> -. ps ) -> ps )";
}
