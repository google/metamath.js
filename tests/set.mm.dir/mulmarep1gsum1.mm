include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "cmulr.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wceq.mm"
include "cif.mm"
include "wa.mm"
include "simp1.mm"
include "adantr.mm"
include "simp2.mm"
include "3ad2ant3.mm"
include "simpr.mm"
include "mulmarep1el.mm"
include "syl113anc.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "wn.mm"
include "df-ne.mm"
include "biimpi.mm"
include "iffalsed.mm"
include "mpteq2dv.mm"
include "cfn.mm"
include "cmnd.mm"
include "ringmnd.mm"
include "3ad2ant1.mm"
include "cvv.mm"
include "matrcl.mm"
include "simpld.mm"
include "3ad2ant2.mm"
include "wb.mm"
include "eqcom.mm"
include "ifbi.mm"
include "oveq2.mm"
include "adantl.mm"
include "ifeq1da.mm"
include "eqtrd.mm"
include "ax-mp.mm"
include "mpteq2i.mm"
include "cbs.mm"
include "eleq2i.mm"
include "eqid.mm"
include "matecl.mm"
include "syl3anc.mm"
include "gsummptif1n0.mm"
include "3eqtrd.mm"

theorem mulmarep1gsum1
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let c.1: class .1.
  let cE: class E
  let cI: class I
  let cJ: class J
  let cK: class K
  let cN: class N
  let cV: class V
  let cX: class X
  let c.0: class .0.
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
  assert |- ( ( R e. Ring /\ ( X e. B /\ C e. V /\ K e. N ) /\ ( I e. N /\ J e. N /\ J =/= K ) ) -> ( R gsum ( l e. N |-> ( ( I X l ) ( .r ` R ) ( l E J ) ) ) ) = ( I X J ) )

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
    cJ
    cK
    wne
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
    @10
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
    cR
    vl
    cN
    cJ
    cK
    wceq
    #
    @11
    @10
    cC
    cfv
    @12
    co
    #
    cJ
    @10
    wceq
    #
    @11
    c.0
    cif
    #
    cif
    #
    cmpt
    #
    cgsu
    co
    cR
    vl
    cN
    @18
    cmpt
    #
    cgsu
    co
    cI
    cJ
    cX
    co
    #
    @9
    @14
    @20
    cR
    cgsu
    @9
    vl
    cN
    @13
    @19
    @9
    @10
    cN
    wcel
    #
    wa
    @0
    @4
    @5
    @6
    @23
    @13
    @19
    wceq
    @9
    @0
    @23
    @0
    @4
    @8
    simp1
    adantr
    @9
    @4
    @23
    @0
    @4
    @8
    simp2
    adantr
    @9
    @5
    @23
    @8
    @0
    @5
    @4
    @5
    @6
    @7
    simp1
    3ad2ant3
    #
    adantr
    @9
    @6
    @23
    @8
    @0
    @6
    @4
    @5
    @6
    @7
    simp2
    3ad2ant3
    #
    adantr
    @9
    @23
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
    @10
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
    syl113anc
    mpteq2dva
    oveq2d
    @9
    @20
    @21
    cR
    cgsu
    @9
    vl
    cN
    @19
    @18
    @9
    @15
    @16
    @18
    @8
    @0
    @15
    wn
    #
    @4
    @7
    @5
    @26
    @6
    @7
    @26
    cJ
    cK
    df-ne
    biimpi
    3ad2ant3
    3ad2ant3
    iffalsed
    mpteq2dv
    oveq2d
    @9
    @22
    vl
    @21
    cR
    cN
    cfn
    cJ
    c.0
    mulmarep1el.0
    @0
    @4
    cR
    cmnd
    wcel
    @8
    cR
    ringmnd
    3ad2ant1
    @4
    @0
    cN
    cfn
    wcel
    #
    @8
    @1
    @2
    @27
    @3
    @1
    @27
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
    @25
    vl
    cN
    @18
    @10
    cJ
    wceq
    #
    @22
    c.0
    cif
    #
    @17
    @28
    wb
    #
    @18
    @29
    wceq
    cJ
    @10
    eqcom
    @30
    @18
    @28
    @11
    c.0
    cif
    @29
    @17
    @28
    @11
    c.0
    ifbi
    @30
    @28
    @11
    @22
    c.0
    @28
    @11
    @22
    wceq
    @30
    @10
    cJ
    cI
    cX
    oveq2
    adantl
    ifeq1da
    eqtrd
    ax-mp
    mpteq2i
    @9
    @5
    @6
    cX
    cA
    cbs
    cfv
    #
    wcel
    #
    @22
    cR
    cbs
    cfv
    #
    wcel
    @24
    @25
    @4
    @0
    @32
    @8
    @1
    @2
    @32
    @3
    @1
    @32
    cB
    @31
    cX
    marepvcl.b
    eleq2i
    biimpi
    3ad2ant1
    3ad2ant2
    cA
    cR
    cI
    cJ
    @33
    cX
    cN
    marepvcl.a
    @33
    eqid
    matecl
    syl3anc
    gsummptif1n0
    3eqtrd
end
