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
include "wb.mm"
include "cvv.mm"
include "wcel.mm"
include "vex.mm"
include "dmex.mm"
include "syl6eqelr.mm"
include "fornex.mm"
include "mpcom.mm"
include "0sdomg.mm"
include "adantl.mm"
include "mpbird.mm"
include "ex.mm"
include "wi.mm"
include "fodomg.mm"
include "a1i.mm"
include "jcad.mm"
include "exlimdv.mm"
include "imp.mm"
include "sdomdomtr.mm"
include "reldom.mm"
include "brrelex2i.mm"
include "mpbid.mm"
include "fodomr.mm"
include "jca.mm"
include "impbii.mm"

theorem fodomb
  let cA: class A
  let cB: class B
  let vf: setvar f

  disjoint A f
  disjoint B f
  assert |- ( ( A =/= (/) /\ E. f f : A -onto-> B ) <-> ( (/) ~< B /\ B ~<_ A ) )

  proof
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
    @3
    @6
    @0
    @2
    @6
    vf
    @0
    @2
    @4
    @5
    @0
    @2
    @4
    @0
    @2
    wa
    @4
    cB
    c0
    wne
    #
    @2
    @0
    @7
    @2
    cA
    c0
    cB
    c0
    @2
    @1
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
    @2
    @8
    cA
    c0
    @2
    cA
    cB
    @1
    wf
    @8
    cA
    wceq
    cA
    cB
    @1
    fof
    cA
    cB
    @1
    fdm
    syl
    #
    eqeq1d
    @9
    @1
    crn
    #
    c0
    wceq
    @2
    @10
    @1
    dm0rn0
    @2
    @12
    cB
    c0
    cA
    cB
    @1
    forn
    eqeq1d
    syl5bb
    bitr3d
    necon3bid
    biimpac
    @2
    @4
    @7
    wb
    #
    @0
    @2
    cB
    cvv
    wcel
    #
    @13
    cA
    cvv
    wcel
    #
    @2
    @14
    @2
    cA
    @8
    cvv
    @11
    @1
    vf
    vex
    dmex
    syl6eqelr
    #
    cA
    cB
    cvv
    @1
    fornex
    mpcom
    cB
    cvv
    0sdomg
    syl
    adantl
    mpbird
    ex
    @2
    @5
    wi
    @0
    @15
    @2
    @5
    @16
    cA
    cB
    cvv
    @1
    fodomg
    mpcom
    a1i
    jcad
    exlimdv
    imp
    @6
    @0
    @3
    @6
    c0
    cA
    csdm
    wbr
    #
    @0
    c0
    cB
    cA
    sdomdomtr
    @6
    @15
    @17
    @0
    wb
    @5
    @15
    @4
    cB
    cA
    cdom
    reldom
    brrelex2i
    adantl
    cA
    cvv
    0sdomg
    syl
    mpbid
    cA
    cB
    vf
    fodomr
    jca
    impbii
end
