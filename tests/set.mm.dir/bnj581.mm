include "cv.mm"
include "wsbc.mm"
include "wfn.mm"
include "w3a.mm"
include "sbcbii.mm"
include "sbc3an.mm"
include "bnj62.mm"
include "bicomi.mm"
include "3anbi123i.mm"
include "bitr4i.mm"
include "3bitri.mm"

theorem bnj581
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vf: setvar f
  let vg: setvar g
  let vn: setvar n
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  let bnjwchm: wff ch'
  assume bnj581.3: |- ( ch <-> ( f Fn n /\ ph /\ ps ) )
  assume bnj581.4: |- ( ph' <-> [. g / f ]. ph )
  assume bnj581.5: |- ( ps' <-> [. g / f ]. ps )
  assume bnj581.6: |- ( ch' <-> [. g / f ]. ch )

  disjoint f n
  assert |- ( ch' <-> ( g Fn n /\ ph' /\ ps' ) )

  proof
    bnjwchm
    wch
    vf
    vg
    cv
    #
    wsbc
    vf
    cv
    vn
    cv
    #
    wfn
    #
    wph
    wps
    w3a
    #
    vf
    @0
    wsbc
    #
    @0
    @1
    wfn
    #
    bnjwphm
    bnjwpsm
    w3a
    #
    bnj581.6
    wch
    @3
    vf
    @0
    bnj581.3
    sbcbii
    @4
    @2
    vf
    @0
    wsbc
    #
    wph
    vf
    @0
    wsbc
    #
    wps
    vf
    @0
    wsbc
    #
    w3a
    @6
    @2
    wph
    wps
    vf
    @0
    sbc3an
    @5
    @7
    bnjwphm
    @8
    bnjwpsm
    @9
    @7
    @5
    vf
    vg
    @1
    bnj62
    bicomi
    bnj581.4
    bnj581.5
    3anbi123i
    bitr4i
    3bitri
end
