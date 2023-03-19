include "cv.mm"
include "wsbc.mm"
include "c0.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "wceq.mm"
include "sbcbii.mm"
include "vex.mm"
include "weq.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "sbcie.mm"
include "3bitri.mm"

theorem bnj154
  let vx: setvar x
  let cA: class A
  let cR: class R
  let vf: setvar f
  let vg: setvar g
  let bnjwphm: wff ph'
  let bnjwph1: wff ph1
  assume bnj154.1: |- ( ph1 <-> [. g / f ]. ph' )
  assume bnj154.2: |- ( ph' <-> ( f ` (/) ) = _pred ( x , A , R ) )

  disjoint A f
  disjoint R f
  disjoint f g
  disjoint f x
  assert |- ( ph1 <-> ( g ` (/) ) = _pred ( x , A , R ) )

  proof
    bnjwph1
    bnjwphm
    vf
    vg
    cv
    #
    wsbc
    c0
    vf
    cv
    #
    cfv
    #
    cA
    cR
    vx
    cv
    c-bnj14
    #
    wceq
    #
    vf
    @0
    wsbc
    c0
    @0
    cfv
    #
    @3
    wceq
    #
    bnj154.1
    bnjwphm
    @4
    vf
    @0
    bnj154.2
    sbcbii
    @4
    @6
    vf
    @0
    vg
    vex
    vf
    vg
    weq
    @2
    @5
    @3
    c0
    @1
    @0
    fveq1
    eqeq1d
    sbcie
    3bitri
end
