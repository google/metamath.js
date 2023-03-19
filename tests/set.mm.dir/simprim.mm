include "idd.mm"
include "impi.mm"

theorem simprim
  param wph: wff ph
  param wps: wff ps


  assert |- ( -. ( ph -> -. ps ) -> ps )

  proof
    wph
    wps
    wps
    wph
    wps
    idd
    impi
end
