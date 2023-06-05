include "id.mm";
include "jca.mm";

theorem ancli(wph: wff ph, wps: wff ps) {
  assume ancli.1: |- "( ph -> ps )";





  do {
    wph;
    wph;
    wps;
    wph;
    id;
    ancli.1;
    jca;
  };

  return |- "( ph -> ( ph /\\ ps ) )";
}
