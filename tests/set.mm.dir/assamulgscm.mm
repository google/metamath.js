include "cn0.mm"
include "wcel.mm"
include "w3a.mm"
include "casa.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wa.mm"
include "cv.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "assamulgscmlem1.mm"
include "assamulgscmlem2.mm"
include "a2d.mm"
include "nn0ind.mm"
include "exp4c.mm"
include "3imp.mm"
include "impcom.mm"

theorem assamulgscm
  let cA: class A
  let cB: class B
  let c.x: class .x.
  let cE: class E
  let c.ex: class .^
  let cF: class F
  let cG: class G
  let cH: class H
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume assamulgscm.v: |- V = ( Base ` W )
  assume assamulgscm.f: |- F = ( Scalar ` W )
  assume assamulgscm.b: |- B = ( Base ` F )
  assume assamulgscm.s: |- .x. = ( .s ` W )
  assume assamulgscm.g: |- G = ( mulGrp ` F )
  assume assamulgscm.p: |- .^ = ( .g ` G )
  assume assamulgscm.h: |- H = ( mulGrp ` W )
  assume assamulgscm.e: |- E = ( .g ` H )


  assert |- ( ( W e. AssAlg /\ ( N e. NN0 /\ A e. B /\ X e. V ) ) -> ( N E ( A .x. X ) ) = ( ( N .^ A ) .x. ( N E X ) ) )

  proof
    cN
    cn0
    wcel
    #
    cA
    cB
    wcel
    #
    cX
    cV
    wcel
    #
    w3a
    cW
    casa
    wcel
    #
    cN
    cA
    cX
    c.x
    co
    #
    cE
    co
    #
    cN
    cA
    c.ex
    co
    #
    cN
    cX
    cE
    co
    #
    c.x
    co
    #
    wceq
    #
    @0
    @1
    @2
    @3
    @9
    wi
    @0
    @1
    @2
    @3
    @9
    @1
    @2
    wa
    @3
    wa
    #
    vx
    cv
    #
    @4
    cE
    co
    #
    @11
    cA
    c.ex
    co
    #
    @11
    cX
    cE
    co
    #
    c.x
    co
    #
    wceq
    #
    wi
    @10
    cc0
    @4
    cE
    co
    #
    cc0
    cA
    c.ex
    co
    #
    cc0
    cX
    cE
    co
    #
    c.x
    co
    #
    wceq
    #
    wi
    @10
    vy
    cv
    #
    @4
    cE
    co
    #
    @22
    cA
    c.ex
    co
    #
    @22
    cX
    cE
    co
    #
    c.x
    co
    #
    wceq
    #
    wi
    @10
    @22
    c1
    caddc
    co
    #
    @4
    cE
    co
    #
    @28
    cA
    c.ex
    co
    #
    @28
    cX
    cE
    co
    #
    c.x
    co
    #
    wceq
    #
    wi
    @10
    @9
    wi
    vx
    vy
    cN
    @11
    cc0
    wceq
    #
    @16
    @21
    @10
    @34
    @12
    @17
    @15
    @20
    @11
    cc0
    @4
    cE
    oveq1
    @34
    @13
    @18
    @14
    @19
    c.x
    @11
    cc0
    cA
    c.ex
    oveq1
    @11
    cc0
    cX
    cE
    oveq1
    oveq12d
    eqeq12d
    imbi2d
    vx
    vy
    weq
    #
    @16
    @27
    @10
    @35
    @12
    @23
    @15
    @26
    @11
    @22
    @4
    cE
    oveq1
    @35
    @13
    @24
    @14
    @25
    c.x
    @11
    @22
    cA
    c.ex
    oveq1
    @11
    @22
    cX
    cE
    oveq1
    oveq12d
    eqeq12d
    imbi2d
    @11
    @28
    wceq
    #
    @16
    @33
    @10
    @36
    @12
    @29
    @15
    @32
    @11
    @28
    @4
    cE
    oveq1
    @36
    @13
    @30
    @14
    @31
    c.x
    @11
    @28
    cA
    c.ex
    oveq1
    @11
    @28
    cX
    cE
    oveq1
    oveq12d
    eqeq12d
    imbi2d
    @11
    cN
    wceq
    #
    @16
    @9
    @10
    @37
    @12
    @5
    @15
    @8
    @11
    cN
    @4
    cE
    oveq1
    @37
    @13
    @6
    @14
    @7
    c.x
    @11
    cN
    cA
    c.ex
    oveq1
    @11
    cN
    cX
    cE
    oveq1
    oveq12d
    eqeq12d
    imbi2d
    cA
    cB
    c.x
    cE
    c.ex
    cF
    cG
    cH
    cV
    cW
    cX
    assamulgscm.v
    assamulgscm.f
    assamulgscm.b
    assamulgscm.s
    assamulgscm.g
    assamulgscm.p
    assamulgscm.h
    assamulgscm.e
    assamulgscmlem1
    @22
    cn0
    wcel
    @10
    @27
    @33
    vy
    cA
    cB
    c.x
    cE
    c.ex
    cF
    cG
    cH
    cV
    cW
    cX
    assamulgscm.v
    assamulgscm.f
    assamulgscm.b
    assamulgscm.s
    assamulgscm.g
    assamulgscm.p
    assamulgscm.h
    assamulgscm.e
    assamulgscmlem2
    a2d
    nn0ind
    exp4c
    3imp
    impcom
end
