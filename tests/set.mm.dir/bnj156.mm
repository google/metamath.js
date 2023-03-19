include "cv.mm"
include "wsbc.mm"
include "c1o.mm"
include "wfn.mm"
include "w3a.mm"
include "sbcbii.mm"
include "sbc3an.mm"
include "bnj62.mm"
include "bicomi.mm"
include "3anbi123i.mm"
include "bitri.mm"

theorem bnj156
  let vf: setvar f
  let vg: setvar g
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  let bnjwze0: wff ze0
  let bnjwph1: wff ph1
  let bnjwps1: wff ps1
  let bnjwze1: wff ze1
  assume bnj156.1: |- ( ze0 <-> ( f Fn 1o /\ ph' /\ ps' ) )
  assume bnj156.2: |- ( ze1 <-> [. g / f ]. ze0 )
  assume bnj156.3: |- ( ph1 <-> [. g / f ]. ph' )
  assume bnj156.4: |- ( ps1 <-> [. g / f ]. ps' )


  assert |- ( ze1 <-> ( g Fn 1o /\ ph1 /\ ps1 ) )

  proof
    bnjwze1
    bnjwze0
    vf
    vg
    cv
    #
    wsbc
    #
    @0
    c1o
    wfn
    #
    bnjwph1
    bnjwps1
    w3a
    #
    bnj156.2
    @1
    vf
    cv
    c1o
    wfn
    #
    bnjwphm
    bnjwpsm
    w3a
    #
    vf
    @0
    wsbc
    #
    @3
    bnjwze0
    @5
    vf
    @0
    bnj156.1
    sbcbii
    @6
    @4
    vf
    @0
    wsbc
    #
    bnjwphm
    vf
    @0
    wsbc
    #
    bnjwpsm
    vf
    @0
    wsbc
    #
    w3a
    @3
    @4
    bnjwphm
    bnjwpsm
    vf
    @0
    sbc3an
    @7
    @2
    @8
    bnjwph1
    @9
    bnjwps1
    vf
    vg
    c1o
    bnj62
    bnjwph1
    @8
    bnj156.3
    bicomi
    bnjwps1
    @9
    bnj156.4
    bicomi
    3anbi123i
    bitri
    bitri
    bitri
end
