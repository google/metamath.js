include "wo.mm"
include "wa.mm"
include "wcad.mm"
include "olc.mm"
include "jca.mm"
include "biantrud.mm"
include "w3a.mm"
include "cadan.mm"
include "3anass.mm"
include "bitri.mm"
include "syl6rbbr.mm"

theorem cad1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ch -> ( cadd ( ph , ps , ch ) <-> ( ph \/ ps ) ) )

  proof
    wch
    wph
    wps
    wo
    #
    @0
    wph
    wch
    wo
    #
    wps
    wch
    wo
    #
    wa
    #
    wa
    #
    wph
    wps
    wch
    wcad
    #
    wch
    @3
    @0
    wch
    @1
    @2
    wch
    wph
    olc
    wch
    wps
    olc
    jca
    biantrud
    @5
    @0
    @1
    @2
    w3a
    @4
    wph
    wps
    wch
    cadan
    @0
    @1
    @2
    3anass
    bitri
    syl6rbbr
end
