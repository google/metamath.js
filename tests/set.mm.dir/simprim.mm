include "idd.mm"
include "impi.mm"

theorem simprim
  let wph: wff ph
  let wps: wff ps


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
