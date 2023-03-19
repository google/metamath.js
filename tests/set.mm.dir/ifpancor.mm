include "wa.mm"
include "wif.mm"
include "ancom.mm"
include "ifpdfan2.mm"
include "3bitr3i.mm"

theorem ifpancor
  let wph: wff ph
  let wps: wff ps


  assert |- ( if- ( ph , ps , ph ) <-> if- ( ps , ph , ps ) )

  proof
    wph
    wps
    wa
    wps
    wph
    wa
    wph
    wps
    wph
    wif
    wps
    wph
    wps
    wif
    wph
    wps
    ancom
    wph
    wps
    ifpdfan2
    wps
    wph
    ifpdfan2
    3bitr3i
end
