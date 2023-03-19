include "cphl.mm"
include "wcel.mm"
include "cin.mm"
include "wa.mm"
include "cocv.mm"
include "cfv.mm"
include "cun.mm"
include "cbs.mm"
include "wss.mm"
include "eqid.mm"
include "ocvss.mm"
include "unssi.mm"
include "ocvcss.mm"
include "mpan2.mm"
include "cssi.mm"
include "ineqan12d.mm"
include "unocv.mm"
include "syl6eqr.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "3impib.mm"

theorem cssincl
  let cA: class A
  let cB: class B
  let cC: class C
  let cW: class W
  assume css0.c: |- C = ( CSubSp ` W )


  assert |- ( ( W e. PreHil /\ A e. C /\ B e. C ) -> ( A i^i B ) e. C )

  proof
    cW
    cphl
    wcel
    #
    cA
    cC
    wcel
    #
    cB
    cC
    wcel
    #
    cA
    cB
    cin
    #
    cC
    wcel
    #
    @0
    @4
    @1
    @2
    wa
    #
    cA
    cW
    cocv
    cfv
    #
    cfv
    #
    cB
    @6
    cfv
    #
    cun
    #
    @6
    cfv
    #
    cC
    wcel
    #
    @0
    @9
    cW
    cbs
    cfv
    #
    wss
    @11
    @7
    @8
    @12
    cA
    @6
    @12
    cW
    @12
    eqid
    #
    @6
    eqid
    #
    ocvss
    cB
    @6
    @12
    cW
    @13
    @14
    ocvss
    unssi
    cC
    @9
    @6
    @12
    cW
    @13
    css0.c
    @14
    ocvcss
    mpan2
    @5
    @3
    @10
    cC
    @5
    @3
    @7
    @6
    cfv
    #
    @8
    @6
    cfv
    #
    cin
    @10
    @1
    @2
    cA
    @15
    cB
    @16
    cC
    cA
    @6
    cW
    @14
    css0.c
    cssi
    cC
    cB
    @6
    cW
    @14
    css0.c
    cssi
    ineqan12d
    @7
    @8
    @6
    cW
    @14
    unocv
    syl6eqr
    eleq1d
    syl5ibrcom
    3impib
end
