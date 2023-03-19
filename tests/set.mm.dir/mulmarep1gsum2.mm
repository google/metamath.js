include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cif.mm"
include "wi.mm"
include "wa.mm"
include "simp1.mm"
include "adantr.mm"
include "simpl2.mm"
include "3ad2ant3.mm"
include "simpl32.mm"
include "simpr.mm"
include "3jca.mm"
include "adantll.mm"
include "mulmarep1el.mm"
include "syl.mm"
include "iftrue.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "fveq1.mm"
include "eqcomd.mm"
include "adantl.mm"
include "cbs.mm"
include "eqid.mm"
include "cfn.mm"
include "cvv.mm"
include "matrcl.mm"
include "simpld.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "cmap.mm"
include "mavmulfv.mm"
include "3eqtr2d.mm"
include "ex.mm"
include "wne.mm"
include "mulmarep1gsum1.mm"
include "syl113anc.mm"
include "wn.mm"
include "df-ne.mm"
include "iffalse.mm"
include "sylbi.mm"
include "expcom.mm"
include "pm2.61ine.mm"

theorem mulmarep1gsum2
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let c.xp: class .X.
  let c.1: class .1.
  let cE: class E
  let cI: class I
  let cJ: class J
  let cK: class K
  let cN: class N
  let cV: class V
  let cX: class X
  let c.0: class .0.
  let cZ: class Z
  let vl: setvar l
  let vi: setvar i
  let vj: setvar j
  let cL: class L
  let cM: class M
  assume marepvcl.a: |- A = ( N Mat R )
  assume marepvcl.b: |- B = ( Base ` A )
  assume marepvcl.v: |- V = ( ( Base ` R ) ^m N )
  assume ma1repvcl.1: |- .1. = ( 1r ` A )
  assume mulmarep1el.0: |- .0. = ( 0g ` R )
  assume mulmarep1el.e: |- E = ( ( .1. ( N matRepV R ) C ) ` K )
  assume mulmarep1gsum2.x: |- .X. = ( R maVecMul <. N , N >. )

  disjoint B l
  disjoint C l
  disjoint I l
  disjoint J l
  disjoint K l
  disjoint N l
  disjoint R l
  disjoint V l
  disjoint X l
  disjoint .0. l
  disjoint A l
  disjoint Z l
  disjoint .X. l
  disjoint B i
  disjoint B j
  disjoint i j
  disjoint C i
  disjoint C j
  disjoint K i
  disjoint K j
  disjoint L i
  disjoint L j
  disjoint M i
  disjoint M j
  disjoint N i
  disjoint N j
  disjoint R i
  disjoint R j
  disjoint V i
  disjoint V j
  assert |- ( ( R e. Ring /\ ( X e. B /\ C e. V /\ K e. N ) /\ ( I e. N /\ J e. N /\ ( X .X. C ) = Z ) ) -> ( R gsum ( l e. N |-> ( ( I X l ) ( .r ` R ) ( l E J ) ) ) ) = if ( J = K , ( Z ` I ) , ( I X J ) ) )

  proof
    cR
    crg
    wcel
    #
    cX
    cB
    wcel
    #
    cC
    cV
    wcel
    #
    cK
    cN
    wcel
    #
    w3a
    #
    cI
    cN
    wcel
    #
    cJ
    cN
    wcel
    #
    cX
    cC
    c.xp
    co
    #
    cZ
    wceq
    #
    w3a
    #
    w3a
    #
    cR
    vl
    cN
    cI
    vl
    cv
    #
    cX
    co
    #
    @11
    cJ
    cE
    co
    cR
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cJ
    cK
    wceq
    #
    cI
    cZ
    cfv
    #
    cI
    cJ
    cX
    co
    #
    cif
    #
    wceq
    #
    wi
    cJ
    cK
    @17
    @10
    @21
    @17
    @10
    wa
    #
    @16
    cR
    vl
    cN
    @12
    @11
    cC
    cfv
    @13
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @18
    @20
    @22
    @15
    @24
    cR
    cgsu
    @22
    vl
    cN
    @14
    @23
    @22
    @11
    cN
    wcel
    #
    wa
    #
    @14
    @17
    @23
    cJ
    @11
    wceq
    @12
    c.0
    cif
    #
    cif
    #
    @23
    @27
    @0
    @4
    @5
    @6
    @26
    w3a
    #
    w3a
    #
    @14
    @29
    wceq
    @10
    @26
    @31
    @17
    @10
    @26
    wa
    #
    @0
    @4
    @30
    @10
    @0
    @26
    @0
    @4
    @9
    simp1
    #
    adantr
    @0
    @4
    @9
    @26
    simpl2
    @32
    @5
    @6
    @26
    @10
    @5
    @26
    @9
    @0
    @5
    @4
    @5
    @6
    @8
    simp1
    3ad2ant3
    #
    adantr
    @5
    @6
    @8
    @0
    @4
    @26
    simpl32
    @10
    @26
    simpr
    3jca
    3jca
    adantll
    cA
    cB
    cC
    cR
    c.1
    cE
    cI
    cJ
    cK
    @11
    cN
    cV
    cX
    c.0
    marepvcl.a
    marepvcl.b
    marepvcl.v
    ma1repvcl.1
    mulmarep1el.0
    mulmarep1el.e
    mulmarep1el
    syl
    @22
    @29
    @23
    wceq
    #
    @26
    @17
    @35
    @10
    @17
    @23
    @28
    iftrue
    adantr
    adantr
    eqtrd
    mpteq2dva
    oveq2d
    @22
    @18
    cI
    @7
    cfv
    #
    @25
    @10
    @18
    @36
    wceq
    #
    @17
    @9
    @0
    @37
    @4
    @8
    @5
    @37
    @6
    @8
    @36
    @18
    cI
    @7
    cZ
    fveq1
    eqcomd
    3ad2ant3
    3ad2ant3
    adantl
    @22
    cA
    cR
    cbs
    cfv
    #
    cR
    @13
    c.xp
    vl
    cI
    cN
    crg
    cX
    cC
    marepvcl.a
    mulmarep1gsum2.x
    @38
    eqid
    @13
    eqid
    @10
    @0
    @17
    @33
    adantl
    @10
    cN
    cfn
    wcel
    #
    @17
    @4
    @0
    @39
    @9
    @1
    @2
    @39
    @3
    @1
    @39
    cR
    cvv
    wcel
    cA
    cB
    cR
    cN
    cX
    marepvcl.a
    marepvcl.b
    matrcl
    simpld
    3ad2ant1
    3ad2ant2
    adantl
    @10
    cX
    cA
    cbs
    cfv
    #
    wcel
    #
    @17
    @4
    @0
    @41
    @9
    @1
    @2
    @41
    @3
    @1
    @41
    cB
    @40
    cX
    marepvcl.b
    eleq2i
    biimpi
    3ad2ant1
    3ad2ant2
    adantl
    @10
    cC
    @38
    cN
    cmap
    co
    #
    wcel
    #
    @17
    @4
    @0
    @43
    @9
    @2
    @1
    @43
    @3
    @2
    @43
    cV
    @42
    cC
    marepvcl.v
    eleq2i
    biimpi
    3ad2ant2
    3ad2ant2
    adantl
    @10
    @5
    @17
    @34
    adantl
    mavmulfv
    eqtrd
    @17
    @18
    @20
    wceq
    @10
    @17
    @20
    @18
    @17
    @18
    @19
    iftrue
    eqcomd
    adantr
    3eqtr2d
    ex
    @10
    cJ
    cK
    wne
    #
    @21
    @10
    @44
    wa
    #
    @16
    @19
    @20
    @45
    @0
    @4
    @5
    @6
    @44
    @16
    @19
    wceq
    @10
    @0
    @44
    @33
    adantr
    @0
    @4
    @9
    @44
    simpl2
    @10
    @5
    @44
    @34
    adantr
    @5
    @6
    @8
    @0
    @4
    @44
    simpl32
    @10
    @44
    simpr
    cA
    cB
    cC
    cR
    c.1
    cE
    cI
    cJ
    cK
    cN
    cV
    cX
    c.0
    vl
    marepvcl.a
    marepvcl.b
    marepvcl.v
    ma1repvcl.1
    mulmarep1el.0
    mulmarep1el.e
    mulmarep1gsum1
    syl113anc
    @44
    @19
    @20
    wceq
    #
    @10
    @44
    @17
    wn
    #
    @46
    cJ
    cK
    df-ne
    @47
    @20
    @19
    @17
    @18
    @19
    iffalse
    eqcomd
    sylbi
    adantl
    eqtrd
    expcom
    pm2.61ine
end
