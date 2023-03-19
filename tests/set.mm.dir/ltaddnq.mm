include "cv.mm"
include "cplq.mm"
include "co.mm"
include "cltq.mm"
include "wbr.mm"
include "cnq.mm"
include "wceq.mm"
include "id.mm"
include "oveq1.mm"
include "breq12d.mm"
include "oveq2.mm"
include "breq2d.mm"
include "wcel.mm"
include "wa.mm"
include "c1q.mm"
include "cmq.mm"
include "1lt2nq.mm"
include "ltmnq.mm"
include "mpbii.mm"
include "mulidnq.mm"
include "distrnq.mm"
include "oveq12d.mm"
include "syl5eq.mm"
include "3brtr3d.mm"
include "ltanq.mm"
include "syl5ib.mm"
include "imp.mm"
include "addcomnq.mm"
include "vex.mm"
include "addassnq.mm"
include "caov12.mm"
include "3brtr3g.mm"
include "wb.mm"
include "adantl.mm"
include "mpbird.mm"
include "vtocl2ga.mm"

theorem ltaddnq
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t


  assert |- ( ( A e. Q. /\ B e. Q. ) -> A <Q ( A +Q B ) )

  proof
    vx
    cv
    #
    @0
    vy
    cv
    #
    cplq
    co
    #
    cltq
    wbr
    #
    cA
    cA
    @1
    cplq
    co
    #
    cltq
    wbr
    cA
    cA
    cB
    cplq
    co
    #
    cltq
    wbr
    vx
    vy
    cA
    cB
    cnq
    cnq
    @0
    cA
    wceq
    #
    @0
    cA
    @2
    @4
    cltq
    @6
    id
    @0
    cA
    @1
    cplq
    oveq1
    breq12d
    @1
    cB
    wceq
    @4
    @5
    cA
    cltq
    @1
    cB
    cA
    cplq
    oveq2
    breq2d
    @0
    cnq
    wcel
    #
    @1
    cnq
    wcel
    #
    wa
    #
    @3
    @1
    @0
    cplq
    co
    #
    @1
    @2
    cplq
    co
    #
    cltq
    wbr
    #
    @9
    @2
    @0
    @1
    @1
    cplq
    co
    #
    cplq
    co
    #
    @10
    @11
    cltq
    @7
    @8
    @2
    @14
    cltq
    wbr
    #
    @8
    @1
    @13
    cltq
    wbr
    @7
    @15
    @8
    @1
    c1q
    cmq
    co
    #
    @1
    c1q
    c1q
    cplq
    co
    #
    cmq
    co
    #
    @1
    @13
    cltq
    @8
    c1q
    @17
    cltq
    wbr
    @16
    @18
    cltq
    wbr
    1lt2nq
    c1q
    @17
    @1
    ltmnq
    mpbii
    @1
    mulidnq
    #
    @8
    @18
    @16
    @16
    cplq
    co
    @13
    @1
    c1q
    c1q
    distrnq
    @8
    @16
    @1
    @16
    @1
    cplq
    @19
    @19
    oveq12d
    syl5eq
    3brtr3d
    @1
    @13
    @0
    ltanq
    syl5ib
    imp
    @0
    @1
    addcomnq
    vr
    vs
    vt
    @0
    @1
    @1
    cplq
    vx
    vex
    vy
    vex
    #
    @20
    vr
    cv
    #
    vs
    cv
    #
    addcomnq
    @21
    @22
    vt
    cv
    addassnq
    caov12
    3brtr3g
    @8
    @3
    @12
    wb
    @7
    @0
    @2
    @1
    ltanq
    adantl
    mpbird
    vtocl2ga
end
