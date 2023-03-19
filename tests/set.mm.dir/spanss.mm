include "chil.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "csh.mm"
include "crab.mm"
include "cint.mm"
include "cspn.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "sstr2.mm"
include "ralrimivw.mm"
include "ss2rab.mm"
include "sylibr.mm"
include "intss.mm"
include "syl.mm"
include "adantl.mm"
include "wceq.mm"
include "sstr.mm"
include "ancoms.mm"
include "spanval.mm"
include "adantr.mm"
include "3sstr4d.mm"

theorem spanss
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D


  assert |- ( ( B C_ ~H /\ A C_ B ) -> ( span ` A ) C_ ( span ` B ) )

  proof
    cB
    chil
    wss
    #
    cA
    cB
    wss
    #
    wa
    #
    cA
    vx
    cv
    #
    wss
    #
    vx
    csh
    crab
    #
    cint
    #
    cB
    @3
    wss
    #
    vx
    csh
    crab
    #
    cint
    #
    cA
    cspn
    cfv
    #
    cB
    cspn
    cfv
    #
    @1
    @6
    @9
    wss
    #
    @0
    @1
    @8
    @5
    wss
    #
    @12
    @1
    @7
    @4
    wi
    #
    vx
    csh
    wral
    @13
    @1
    @14
    vx
    csh
    cA
    cB
    @3
    sstr2
    ralrimivw
    @7
    @4
    vx
    csh
    ss2rab
    sylibr
    @8
    @5
    intss
    syl
    adantl
    @2
    cA
    chil
    wss
    #
    @10
    @6
    wceq
    @1
    @0
    @15
    cA
    cB
    chil
    sstr
    ancoms
    vx
    cA
    spanval
    syl
    @0
    @11
    @9
    wceq
    @1
    vx
    cB
    spanval
    adantr
    3sstr4d
end
