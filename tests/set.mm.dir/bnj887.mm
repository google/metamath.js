include "w3a.mm"
include "wa.mm"
include "w-bnj17.mm"
include "3anbi123i.mm"
include "anbi12i.mm"
include "df-bnj17.mm"
include "3bitr4i.mm"

theorem bnj887
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  let bnjwchm: wff ch'
  let bnjwthm: wff th'
  assume bnj887.1: |- ( ph <-> ph' )
  assume bnj887.2: |- ( ps <-> ps' )
  assume bnj887.3: |- ( ch <-> ch' )
  assume bnj887.4: |- ( th <-> th' )


  assert |- ( ( ph /\ ps /\ ch /\ th ) <-> ( ph' /\ ps' /\ ch' /\ th' ) )

  proof
    wph
    wps
    wch
    w3a
    #
    wth
    wa
    bnjwphm
    bnjwpsm
    bnjwchm
    w3a
    #
    bnjwthm
    wa
    wph
    wps
    wch
    wth
    w-bnj17
    bnjwphm
    bnjwpsm
    bnjwchm
    bnjwthm
    w-bnj17
    @0
    @1
    wth
    bnjwthm
    wph
    bnjwphm
    wps
    bnjwpsm
    wch
    bnjwchm
    bnj887.1
    bnj887.2
    bnj887.3
    3anbi123i
    bnj887.4
    anbi12i
    wph
    wps
    wch
    wth
    df-bnj17
    bnjwphm
    bnjwpsm
    bnjwchm
    bnjwthm
    df-bnj17
    3bitr4i
end
