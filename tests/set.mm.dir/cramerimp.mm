include "ccrg.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "cfv.mm"
include "cui.mm"
include "w3a.mm"
include "cmulr.mm"
include "crg.mm"
include "cbs.mm"
include "crngring.mm"
include "adantr.mm"
include "3ad2ant1.mm"
include "wf.mm"
include "eqid.mm"
include "mdetf.mm"
include "cur.mm"
include "cmatrepV.mm"
include "cfn.mm"
include "cvv.mm"
include "matrcl.mm"
include "simpld.mm"
include "anim12i.mm"
include "3adant3.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "anim12ci.mm"
include "anim1i.mm"
include "simpl.mm"
include "3ad2ant3.mm"
include "slesolvec.mm"
include "sylc.mm"
include "simpr.mm"
include "ma1repvcl.mm"
include "syl12anc.mm"
include "syl5eqel.mm"
include "ffvelrnd.mm"
include "dvrcan3.mm"
include "syl3anc.mm"
include "unitcl.mm"
include "adantl.mm"
include "crngcom.mm"
include "oveq1d.mm"
include "3jca.mm"
include "cramerimplem1.mm"
include "syl2anc.mm"
include "3eqtr3rd.mm"
include "cramerimplem3.mm"
include "3adant3r.mm"
include "eqtrd.mm"

theorem cramerimp
  let cA: class A
  let cB: class B
  let cD: class D
  let c.dv: class ./
  let cR: class R
  let c.x: class .x.
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
  assume cramerimp.q: |- ./ = ( /r ` R )


  assert |- ( ( ( R e. CRing /\ I e. N ) /\ ( X e. B /\ Y e. V ) /\ ( ( X .x. Z ) = Y /\ ( D ` X ) e. ( Unit ` R ) ) ) -> ( Z ` I ) = ( ( D ` H ) ./ ( D ` X ) ) )

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
    cX
    cD
    cfv
    #
    cR
    cui
    cfv
    #
    wcel
    #
    wa
    #
    w3a
    #
    cI
    cZ
    cfv
    #
    @7
    cE
    cD
    cfv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    @7
    c.dv
    co
    #
    cH
    cD
    cfv
    #
    @7
    c.dv
    co
    @11
    @13
    @7
    @14
    co
    #
    @7
    c.dv
    co
    #
    @13
    @16
    @12
    @11
    cR
    crg
    wcel
    #
    @13
    cR
    cbs
    cfv
    #
    wcel
    #
    @9
    @19
    @13
    wceq
    @2
    @5
    @20
    @10
    @0
    @20
    @1
    cR
    crngring
    #
    adantr
    #
    3ad2ant1
    @11
    cB
    @21
    cE
    cD
    @2
    @5
    cB
    @21
    cD
    wf
    #
    @10
    @0
    @25
    @1
    cA
    cB
    cD
    cR
    @21
    cN
    cramerimp.d
    cramerimp.a
    cramerimp.b
    @21
    eqid
    #
    mdetf
    adantr
    3ad2ant1
    @11
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
    @11
    @20
    cN
    cfn
    wcel
    #
    wa
    #
    cZ
    cV
    wcel
    #
    @1
    @28
    cB
    wcel
    @2
    @5
    @30
    @10
    @2
    @20
    @5
    @29
    @24
    @3
    @29
    @4
    @3
    @29
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
    anim12i
    3adant3
    @11
    cN
    c0
    wne
    #
    @20
    wa
    #
    @5
    wa
    #
    @6
    @31
    @2
    @5
    @35
    @10
    @2
    @34
    @5
    @0
    @20
    @1
    @33
    @23
    cN
    cI
    ne0i
    anim12ci
    anim1i
    3adant3
    @10
    @2
    @6
    @5
    @6
    @9
    simpl
    3ad2ant3
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
    sylc
    #
    @2
    @5
    @1
    @10
    @0
    @1
    simpr
    #
    3ad2ant1
    cA
    cB
    cZ
    cR
    @27
    cI
    cN
    cV
    cramerimp.a
    cramerimp.b
    cramerimp.v
    @27
    eqid
    ma1repvcl
    syl12anc
    syl5eqel
    ffvelrnd
    #
    @10
    @2
    @9
    @5
    @6
    @9
    simpr
    3ad2ant3
    @21
    c.dv
    cR
    @14
    @8
    @13
    @7
    @26
    @8
    eqid
    #
    cramerimp.q
    @14
    eqid
    #
    dvrcan3
    syl3anc
    @11
    @18
    @15
    @7
    c.dv
    @11
    @0
    @22
    @7
    @21
    wcel
    #
    @18
    @15
    wceq
    @2
    @5
    @0
    @10
    @0
    @1
    simpl
    #
    3ad2ant1
    @38
    @10
    @2
    @41
    @5
    @9
    @41
    @6
    @21
    cR
    @8
    @7
    @26
    @39
    unitcl
    adantl
    3ad2ant3
    @21
    cR
    @14
    @13
    @7
    @26
    @40
    crngcom
    syl3anc
    oveq1d
    @11
    @29
    @0
    @1
    w3a
    #
    @31
    @13
    @12
    wceq
    @2
    @5
    @43
    @10
    @2
    @5
    wa
    @29
    @0
    @1
    @5
    @29
    @2
    @32
    adantl
    @2
    @0
    @5
    @42
    adantr
    @2
    @1
    @5
    @37
    adantr
    3jca
    3adant3
    @36
    cA
    cB
    cD
    cR
    cE
    cI
    cN
    cV
    cZ
    cramerimp.a
    cramerimp.b
    cramerimp.v
    cramerimp.e
    cramerimp.d
    cramerimplem1
    syl2anc
    3eqtr3rd
    @11
    @15
    @17
    @7
    c.dv
    @2
    @5
    @6
    @15
    @17
    wceq
    @9
    cA
    cB
    cD
    cR
    c.x
    @14
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
    cramerimp.d
    @40
    cramerimplem3
    3adant3r
    oveq1d
    eqtrd
end
