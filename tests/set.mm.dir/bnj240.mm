include "wa.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "jca.mm"
include "3comr.mm"

theorem bnj240
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let bnjwpsm: wff ps'
  let bnjwchm: wff ch'
  assume bnj240.1: |- ( ps -> ps' )
  assume bnj240.2: |- ( ch -> ch' )


  assert |- ( ( ph /\ ps /\ ch ) -> ( ps' /\ ch' ) )

  proof
    wps
    wch
    wph
    bnjwpsm
    bnjwchm
    wa
    wps
    wch
    wph
    w3a
    bnjwpsm
    bnjwchm
    wps
    wch
    bnjwpsm
    wph
    bnj240.1
    3ad2ant1
    wch
    wps
    bnjwchm
    wph
    bnj240.2
    3ad2ant2
    jca
    3comr
end
