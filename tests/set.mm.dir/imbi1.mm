include "wb.mm";
include "id.mm";
include "imbi1d.mm";

theorem imbi1(wph: wff ph, wps: wff ps, wch: wff ch) {





  do {
    wph;
    wps;
    wb;
    #;
    wph;
    wps;
    wch;
    @0;
    id;
    imbi1d;
  };

  return |- "( ( ph <-> ps ) -> ( ( ph -> ch ) <-> ( ps -> ch ) ) )";
}
