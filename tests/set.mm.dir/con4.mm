include "ax-3.mm";

theorem con4(wph: wff ph, wps: wff ps) {





  do {
    wph;
    wps;
    ax-3;
  };

  return |- "( ( -. ph -> -. ps ) -> ( ps -> ph ) )";
}
