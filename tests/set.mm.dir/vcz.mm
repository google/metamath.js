include "cvc.mm"
include "wcel.mm"
include "cc.mm"
include "wa.mm"
include "cc0.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "vczcl.mm"
include "anim2i.mm"
include "ancoms.mm"
include "0cn.mm"
include "vcass.mm"
include "mp3anr2.mm"
include "syldan.mm"
include "mul01.mm"
include "oveq1d.mm"
include "vc0.mm"
include "mpdan.mm"
include "sylan9eqr.mm"
include "oveq2d.mm"
include "adantr.mm"
include "3eqtr3rd.mm"

theorem vcz
  let cA: class A
  let cS: class S
  let cG: class G
  let cW: class W
  let cX: class X
  let cZ: class Z
  assume vc0.1: |- G = ( 1st ` W )
  assume vc0.2: |- S = ( 2nd ` W )
  assume vc0.3: |- X = ran G
  assume vc0.4: |- Z = ( GId ` G )


  assert |- ( ( W e. CVecOLD /\ A e. CC ) -> ( A S Z ) = Z )

  proof
    cW
    cvc
    wcel
    #
    cA
    cc
    wcel
    #
    wa
    cA
    cc0
    cmul
    co
    #
    cZ
    cS
    co
    #
    cA
    cc0
    cZ
    cS
    co
    #
    cS
    co
    #
    cZ
    cA
    cZ
    cS
    co
    #
    @0
    @1
    @1
    cZ
    cX
    wcel
    #
    wa
    #
    @3
    @5
    wceq
    #
    @1
    @0
    @8
    @0
    @7
    @1
    cG
    cW
    cX
    cZ
    vc0.1
    vc0.3
    vc0.4
    vczcl
    #
    anim2i
    ancoms
    @0
    @1
    cc0
    cc
    wcel
    @7
    @9
    0cn
    cA
    cc0
    cZ
    cS
    cG
    cW
    cX
    vc0.1
    vc0.2
    vc0.3
    vcass
    mp3anr2
    syldan
    @1
    @0
    @3
    @4
    cZ
    @1
    @2
    cc0
    cZ
    cS
    cA
    mul01
    oveq1d
    @0
    @7
    @4
    cZ
    wceq
    @10
    cZ
    cS
    cG
    cW
    cX
    cZ
    vc0.1
    vc0.2
    vc0.3
    vc0.4
    vc0
    mpdan
    #
    sylan9eqr
    @0
    @5
    @6
    wceq
    @1
    @0
    @4
    cZ
    cA
    cS
    @11
    oveq2d
    adantr
    3eqtr3rd
end
