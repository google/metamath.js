include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cmulr.mm"
include "cfv.mm"
include "wceq.mm"
include "cur.mm"
include "cif.mm"
include "wa.mm"
include "simp3.mm"
include "simp2.mm"
include "jca.mm"
include "ma1repveval.mm"
include "syl3an3.mm"
include "oveq2d.mm"
include "ovif2.mm"
include "a1i.mm"
include "cbs.mm"
include "simp1.mm"
include "3ad2ant3.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "eqid.mm"
include "matecl.mm"
include "syl3anc.mm"
include "ringridm.mm"
include "syl2anc.mm"
include "ringrz.mm"
include "ifeq12d.mm"
include "syl5eq.mm"
include "ifeq2d.mm"
include "3eqtrd.mm"

theorem mulmarep1el
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let c.1: class .1.
  let cE: class E
  let cI: class I
  let cJ: class J
  let cK: class K
  let cL: class L
  let cN: class N
  let cV: class V
  let cX: class X
  let c.0: class .0.
  let vi: setvar i
  let vj: setvar j
  let cM: class M
  assume marepvcl.a: |- A = ( N Mat R )
  assume marepvcl.b: |- B = ( Base ` A )
  assume marepvcl.v: |- V = ( ( Base ` R ) ^m N )
  assume ma1repvcl.1: |- .1. = ( 1r ` A )
  assume mulmarep1el.0: |- .0. = ( 0g ` R )
  assume mulmarep1el.e: |- E = ( ( .1. ( N matRepV R ) C ) ` K )


  assert |- ( ( R e. Ring /\ ( X e. B /\ C e. V /\ K e. N ) /\ ( I e. N /\ J e. N /\ L e. N ) ) -> ( ( I X L ) ( .r ` R ) ( L E J ) ) = if ( J = K , ( ( I X L ) ( .r ` R ) ( C ` L ) ) , if ( J = L , ( I X L ) , .0. ) ) )

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
    cL
    cN
    wcel
    #
    w3a
    #
    w3a
    #
    cI
    cL
    cX
    co
    #
    cL
    cJ
    cE
    co
    #
    cR
    cmulr
    cfv
    #
    co
    @10
    cJ
    cK
    wceq
    #
    cL
    cC
    cfv
    #
    cJ
    cL
    wceq
    #
    cR
    cur
    cfv
    #
    c.0
    cif
    #
    cif
    #
    @12
    co
    #
    @13
    @10
    @14
    @12
    co
    #
    @10
    @17
    @12
    co
    #
    cif
    #
    @13
    @20
    @15
    @10
    c.0
    cif
    #
    cif
    @9
    @11
    @18
    @10
    @12
    @8
    @0
    @4
    @7
    @6
    wa
    @11
    @18
    wceq
    @8
    @7
    @6
    @5
    @6
    @7
    simp3
    #
    @5
    @6
    @7
    simp2
    jca
    cA
    cB
    cC
    cR
    c.1
    cE
    cL
    cJ
    cK
    cX
    cN
    cV
    c.0
    marepvcl.a
    marepvcl.b
    marepvcl.v
    ma1repvcl.1
    mulmarep1el.0
    mulmarep1el.e
    ma1repveval
    syl3an3
    oveq2d
    @19
    @22
    wceq
    @9
    @13
    @10
    @14
    @17
    @12
    ovif2
    a1i
    @9
    @13
    @21
    @23
    @20
    @9
    @21
    @15
    @10
    @16
    @12
    co
    #
    @10
    c.0
    @12
    co
    #
    cif
    @23
    @15
    @10
    @16
    c.0
    @12
    ovif2
    @9
    @15
    @25
    @10
    @26
    c.0
    @9
    @0
    @10
    cR
    cbs
    cfv
    #
    wcel
    #
    @25
    @10
    wceq
    @0
    @4
    @8
    simp1
    #
    @9
    @5
    @7
    cX
    cA
    cbs
    cfv
    #
    wcel
    #
    @28
    @8
    @0
    @5
    @4
    @5
    @6
    @7
    simp1
    3ad2ant3
    @8
    @0
    @7
    @4
    @24
    3ad2ant3
    @4
    @0
    @31
    @8
    @1
    @2
    @31
    @3
    @1
    @31
    cB
    @30
    cX
    marepvcl.b
    eleq2i
    biimpi
    3ad2ant1
    3ad2ant2
    cA
    cR
    cI
    cL
    @27
    cX
    cN
    marepvcl.a
    @27
    eqid
    #
    matecl
    syl3anc
    #
    @27
    cR
    @12
    @16
    @10
    @32
    @12
    eqid
    #
    @16
    eqid
    ringridm
    syl2anc
    @9
    @0
    @28
    @26
    c.0
    wceq
    @29
    @33
    @27
    cR
    @12
    @10
    c.0
    @32
    @34
    mulmarep1el.0
    ringrz
    syl2anc
    ifeq12d
    syl5eq
    ifeq2d
    3eqtrd
end
