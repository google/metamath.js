include "ccrg.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "cotp.mm"
include "cmmul.mm"
include "cfv.mm"
include "cmulr.mm"
include "cfn.mm"
include "simpl.mm"
include "cvv.mm"
include "matrcl.mm"
include "simpld.mm"
include "adantr.mm"
include "anim12ci.mm"
include "3adant3.mm"
include "eqid.mm"
include "matmulr.mm"
include "syl.mm"
include "oveqd.mm"
include "fveq2d.mm"
include "cramerimplem2.mm"
include "simp1l.mm"
include "simp2l.mm"
include "cur.mm"
include "cmatrepV.mm"
include "crg.mm"
include "crngring.mm"
include "anim12i.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "ne0i.mm"
include "slesolvec.mm"
include "sylan.mm"
include "3impia.mm"
include "simp1r.mm"
include "ma1repvcl.mm"
include "syl12anc.mm"
include "syl5eqel.mm"
include "mdetmul.mm"
include "syl3anc.mm"
include "3eqtr3rd.mm"

theorem cramerimplem3
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let c.x: class .x.
  let c.xo: class .(x)
  let cE: class E
  let cH: class H
  let cI: class I
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume cramerimp.a: |- A = ( N Mat R )
  assume cramerimp.b: |- B = ( Base ` A )
  assume cramerimp.v: |- V = ( ( Base ` R ) ^m N )
  assume cramerimp.e: |- E = ( ( ( 1r ` A ) ( N matRepV R ) Z ) ` I )
  assume cramerimp.h: |- H = ( ( X ( N matRepV R ) Y ) ` I )
  assume cramerimp.x: |- .x. = ( R maVecMul <. N , N >. )
  assume cramerimp.d: |- D = ( N maDet R )
  assume cramerimp.t: |- .(x) = ( .r ` R )


  assert |- ( ( ( R e. CRing /\ I e. N ) /\ ( X e. B /\ Y e. V ) /\ ( X .x. Z ) = Y ) -> ( ( D ` X ) .(x) ( D ` E ) ) = ( D ` H ) )

  proof
    cR
    ccrg
    wcel
    #
    cI
    cN
    wcel
    #
    wa
    #
    cX
    cB
    wcel
    #
    cY
    cV
    wcel
    #
    wa
    #
    cX
    cZ
    c.x
    co
    cY
    wceq
    #
    w3a
    #
    cX
    cE
    cR
    cN
    cN
    cN
    cotp
    cmmul
    co
    #
    co
    #
    cD
    cfv
    cX
    cE
    cA
    cmulr
    cfv
    #
    co
    #
    cD
    cfv
    #
    cH
    cD
    cfv
    cX
    cD
    cfv
    cE
    cD
    cfv
    c.xo
    co
    #
    @7
    @9
    @11
    cD
    @7
    @8
    @10
    cX
    cE
    @7
    cN
    cfn
    wcel
    #
    @0
    wa
    #
    @8
    @10
    wceq
    @2
    @5
    @15
    @6
    @2
    @0
    @5
    @14
    @0
    @1
    simpl
    @3
    @14
    @4
    @3
    @14
    cR
    cvv
    wcel
    cA
    cB
    cR
    cN
    cX
    cramerimp.a
    cramerimp.b
    matrcl
    simpld
    adantr
    #
    anim12ci
    3adant3
    cA
    cR
    @8
    cN
    ccrg
    cramerimp.a
    @8
    eqid
    #
    matmulr
    syl
    oveqd
    fveq2d
    @7
    @9
    cH
    cD
    cA
    cB
    cR
    c.x
    @8
    cE
    cH
    cI
    cN
    cV
    cX
    cY
    cZ
    cramerimp.a
    cramerimp.b
    cramerimp.v
    cramerimp.e
    cramerimp.h
    cramerimp.x
    @17
    cramerimplem2
    fveq2d
    @7
    @0
    @3
    cE
    cB
    wcel
    @12
    @13
    wceq
    @0
    @1
    @5
    @6
    simp1l
    @2
    @3
    @4
    @6
    simp2l
    @7
    cE
    cI
    cA
    cur
    cfv
    #
    cZ
    cN
    cR
    cmatrepV
    co
    co
    cfv
    #
    cB
    cramerimp.e
    @7
    cR
    crg
    wcel
    #
    @14
    wa
    #
    cZ
    cV
    wcel
    #
    @1
    @19
    cB
    wcel
    @2
    @5
    @21
    @6
    @2
    @20
    @5
    @14
    @0
    @20
    @1
    cR
    crngring
    #
    adantr
    @16
    anim12i
    3adant3
    @2
    @5
    @6
    @22
    @2
    cN
    c0
    wne
    #
    @20
    wa
    @5
    @6
    @22
    wi
    @0
    @20
    @1
    @24
    @23
    cN
    cI
    ne0i
    anim12ci
    cA
    cB
    cR
    c.x
    cN
    cV
    cX
    cY
    cZ
    cramerimp.a
    cramerimp.b
    cramerimp.v
    cramerimp.x
    slesolvec
    sylan
    3impia
    @0
    @1
    @5
    @6
    simp1r
    cA
    cB
    cZ
    cR
    @18
    cI
    cN
    cV
    cramerimp.a
    cramerimp.b
    cramerimp.v
    @18
    eqid
    ma1repvcl
    syl12anc
    syl5eqel
    cA
    cB
    cD
    cR
    @10
    c.xo
    cX
    cE
    cN
    cramerimp.a
    cramerimp.b
    cramerimp.d
    cramerimp.t
    @10
    eqid
    mdetmul
    syl3anc
    3eqtr3rd
end
