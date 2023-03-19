include "cfix.mm"
include "cid.mm"
include "cin.mm"
include "crn.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "vex.mm"
include "elfix.mm"
include "wex.mm"
include "weq.mm"
include "wa.mm"
include "elrn.mm"
include "brin.mm"
include "ancom.mm"
include "ideq.mm"
include "anbi1i.mm"
include "3bitri.mm"
include "exbii.mm"
include "breq1.mm"
include "ceqsexv.mm"
include "bitr4i.mm"
include "eqriv.mm"

theorem dffix2
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- Fix A = ran ( A i^i _I )

  proof
    vx
    cA
    cfix
    #
    cA
    cid
    cin
    #
    crn
    #
    vx
    cv
    #
    @0
    wcel
    @3
    @3
    cA
    wbr
    #
    @3
    @2
    wcel
    #
    @3
    cA
    vx
    vex
    #
    elfix
    @5
    vy
    cv
    #
    @3
    @1
    wbr
    #
    vy
    wex
    vy
    vx
    weq
    #
    @7
    @3
    cA
    wbr
    #
    wa
    #
    vy
    wex
    @4
    vy
    @3
    @1
    @6
    elrn
    @8
    @11
    vy
    @8
    @10
    @7
    @3
    cid
    wbr
    #
    wa
    @12
    @10
    wa
    @11
    @7
    @3
    cA
    cid
    brin
    @10
    @12
    ancom
    @12
    @9
    @10
    @7
    @3
    @6
    ideq
    anbi1i
    3bitri
    exbii
    @10
    @4
    vy
    @3
    @6
    @7
    @3
    @3
    cA
    breq1
    ceqsexv
    3bitri
    bitr4i
    eqriv
end
