include "wb.mm"
include "wn.mm"
include "xor3.mm"
include "biimpi.mm"
include "orri.mm"

theorem pm5.15
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph <-> ps ) \/ ( ph <-> -. ps ) )

  proof
    wph
    wps
    wb
    #
    wph
    wps
    wn
    wb
    #
    @0
    wn
    @1
    wph
    wps
    xor3
    biimpi
    orri
end
