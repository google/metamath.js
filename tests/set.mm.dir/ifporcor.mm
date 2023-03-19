include "wo.mm"
include "wif.mm"
include "orcom.mm"
include "ifpdfor2.mm"
include "3bitr3i.mm"

theorem ifporcor
  let wph: wff ph
  let wps: wff ps


  assert |- ( if- ( ph , ph , ps ) <-> if- ( ps , ps , ph ) )

  proof
    wph
    wps
    wo
    wps
    wph
    wo
    wph
    wph
    wps
    wif
    wps
    wps
    wph
    wif
    wph
    wps
    orcom
    wph
    wps
    ifpdfor2
    wps
    wph
    ifpdfor2
    3bitr3i
end
