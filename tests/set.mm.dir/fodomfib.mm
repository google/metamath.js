include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wfo.mm"
include "wex.mm"
include "wa.mm"
include "csdm.mm"
include "wbr.mm"
include "cdom.mm"
include "cdm.mm"
include "wceq.mm"
include "wf.mm"
include "fof.mm"
include "fdm.mm"
include "syl.mm"
include "eqeq1d.mm"
include "crn.mm"
include "dm0rn0.mm"
include "forn.mm"
include "syl5bb.mm"
include "bitr3d.mm"
include "necon3bid.mm"
include "biimpac.mm"
include "adantll.mm"
include "wb.mm"
include "cvv.mm"
include "vex.mm"
include "rnex.mm"
include "syl6eqelr.mm"
include "adantl.mm"
include "0sdomg.mm"
include "adantlr.mm"
include "mpbird.mm"
include "ex.mm"
include "wi.mm"
include "fodomfi.mm"
include "adantr.mm"
include "jcad.mm"
include "exlimdv.mm"
include "expimpd.mm"
include "sdomdomtr.mm"
include "syl5ib.mm"
include "fodomr.mm"
include "a1i.mm"
include "impbid.mm"

theorem fodomfib
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F

  disjoint A f
  disjoint B f
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F x
  disjoint F y
  disjoint F z
  assert |- ( A e. Fin -> ( ( A =/= (/) /\ E. f f : A -onto-> B ) <-> ( (/) ~< B /\ B ~<_ A ) ) )

  proof
    cA
    cfn
    wcel
    #
    cA
    c0
    wne
    #
    cA
    cB
    vf
    cv
    #
    wfo
    #
    vf
    wex
    #
    wa
    c0
    cB
    csdm
    wbr
    #
    cB
    cA
    cdom
    wbr
    #
    wa
    #
    @0
    @1
    @4
    @7
    @0
    @1
    wa
    #
    @3
    @7
    vf
    @8
    @3
    @5
    @6
    @8
    @3
    @5
    @8
    @3
    wa
    @5
    cB
    c0
    wne
    #
    @1
    @3
    @9
    @0
    @3
    @1
    @9
    @3
    cA
    c0
    cB
    c0
    @3
    @2
    cdm
    #
    c0
    wceq
    #
    cA
    c0
    wceq
    cB
    c0
    wceq
    #
    @3
    @10
    cA
    c0
    @3
    cA
    cB
    @2
    wf
    @10
    cA
    wceq
    cA
    cB
    @2
    fof
    cA
    cB
    @2
    fdm
    syl
    eqeq1d
    @11
    @2
    crn
    #
    c0
    wceq
    @3
    @12
    @2
    dm0rn0
    @3
    @13
    cB
    c0
    cA
    cB
    @2
    forn
    #
    eqeq1d
    syl5bb
    bitr3d
    necon3bid
    biimpac
    adantll
    @0
    @3
    @5
    @9
    wb
    #
    @1
    @0
    @3
    wa
    cB
    cvv
    wcel
    #
    @15
    @3
    @16
    @0
    @3
    cB
    @13
    cvv
    @14
    @2
    vf
    vex
    rnex
    syl6eqelr
    adantl
    cB
    cvv
    0sdomg
    syl
    adantlr
    mpbird
    ex
    @0
    @3
    @6
    wi
    @1
    @0
    @3
    @6
    cA
    cB
    @2
    fodomfi
    ex
    adantr
    jcad
    exlimdv
    expimpd
    @0
    @7
    @1
    @4
    @7
    c0
    cA
    csdm
    wbr
    @0
    @1
    c0
    cB
    cA
    sdomdomtr
    cA
    cfn
    0sdomg
    syl5ib
    @7
    @4
    wi
    @0
    cA
    cB
    vf
    fodomr
    a1i
    jcad
    impbid
end
