include "w3a.mm"
include "wsbc.mm"
include "sbc3an.mm"
include "bicomi.mm"
include "3anbi123i.mm"
include "bitri.mm"

theorem bnj206
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vn: setvar n
  let cM: class M
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  let bnjwchm: wff ch'
  assume bnj206.1: |- ( ph' <-> [. M / n ]. ph )
  assume bnj206.2: |- ( ps' <-> [. M / n ]. ps )
  assume bnj206.3: |- ( ch' <-> [. M / n ]. ch )
  assume bnj206.4: |- M e. _V


  assert |- ( [. M / n ]. ( ph /\ ps /\ ch ) <-> ( ph' /\ ps' /\ ch' ) )

  proof
    wph
    wps
    wch
    w3a
    vn
    cM
    wsbc
    wph
    vn
    cM
    wsbc
    #
    wps
    vn
    cM
    wsbc
    #
    wch
    vn
    cM
    wsbc
    #
    w3a
    bnjwphm
    bnjwpsm
    bnjwchm
    w3a
    wph
    wps
    wch
    vn
    cM
    sbc3an
    @0
    bnjwphm
    @1
    bnjwpsm
    @2
    bnjwchm
    bnjwphm
    @0
    bnj206.1
    bicomi
    bnjwpsm
    @1
    bnj206.2
    bicomi
    bnjwchm
    @2
    bnj206.3
    bicomi
    3anbi123i
    bitri
end
