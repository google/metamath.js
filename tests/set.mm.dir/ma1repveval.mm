include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "cfv.mm"
include "cif.mm"
include "cur.mm"
include "wi.mm"
include "cfn.mm"
include "cvv.mm"
include "matrcl.mm"
include "simpld.mm"
include "cmat.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "mat1bas.mm"
include "expcom.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "impcom.mm"
include "simpr2.mm"
include "simpr3.mm"
include "3jca.mm"
include "cmatrepV.mm"
include "a1i.mm"
include "oveqd.mm"
include "eqid.mm"
include "marepveval.mm"
include "eqtrd.mm"
include "stoic3.mm"
include "3ad2ant2.mm"
include "simp1.mm"
include "simp3l.mm"
include "simp3r.mm"
include "mat1ov.mm"
include "wb.mm"
include "eqcom.mm"
include "ifbid.mm"
include "ifeq2d.mm"

theorem ma1repveval
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let c.1: class .1.
  let cE: class E
  let cI: class I
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let cV: class V
  let c.0: class .0.
  let vi: setvar i
  let vj: setvar j
  let cL: class L
  assume marepvcl.a: |- A = ( N Mat R )
  assume marepvcl.b: |- B = ( Base ` A )
  assume marepvcl.v: |- V = ( ( Base ` R ) ^m N )
  assume ma1repvcl.1: |- .1. = ( 1r ` A )
  assume mulmarep1el.0: |- .0. = ( 0g ` R )
  assume mulmarep1el.e: |- E = ( ( .1. ( N matRepV R ) C ) ` K )


  assert |- ( ( R e. Ring /\ ( M e. B /\ C e. V /\ K e. N ) /\ ( I e. N /\ J e. N ) ) -> ( I E J ) = if ( J = K , ( C ` I ) , if ( J = I , ( 1r ` R ) , .0. ) ) )

  proof
    cR
    crg
    wcel
    #
    cM
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
    wa
    #
    w3a
    #
    cI
    cJ
    cE
    co
    #
    cJ
    cK
    wceq
    #
    cI
    cC
    cfv
    #
    cI
    cJ
    c.1
    co
    #
    cif
    #
    @10
    @11
    cJ
    cI
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
    @0
    @4
    c.1
    cB
    wcel
    #
    @2
    @3
    w3a
    #
    @7
    @9
    @13
    wceq
    @0
    @4
    wa
    @17
    @2
    @3
    @4
    @0
    @17
    @1
    @2
    @0
    @17
    wi
    #
    @3
    @1
    cN
    cfn
    wcel
    #
    @19
    @1
    @20
    cR
    cvv
    wcel
    cA
    cB
    cR
    cN
    cM
    marepvcl.a
    marepvcl.b
    matrcl
    simpld
    #
    @0
    @20
    @17
    cA
    cB
    cR
    c.1
    cN
    marepvcl.a
    marepvcl.b
    c.1
    cA
    cur
    cfv
    cN
    cR
    cmat
    co
    #
    cur
    cfv
    ma1repvcl.1
    cA
    @22
    cur
    marepvcl.a
    fveq2i
    eqtri
    mat1bas
    expcom
    syl
    3ad2ant1
    impcom
    @0
    @1
    @2
    @3
    simpr2
    @0
    @1
    @2
    @3
    simpr3
    3jca
    @18
    @7
    wa
    #
    @9
    cI
    cJ
    cK
    c.1
    cC
    cN
    cR
    cmatrepV
    co
    #
    co
    cfv
    #
    co
    @13
    @23
    cE
    @25
    cI
    cJ
    cE
    @25
    wceq
    @23
    mulmarep1el.e
    a1i
    oveqd
    cA
    cB
    cC
    @24
    cR
    cI
    cJ
    cK
    c.1
    cN
    cV
    marepvcl.a
    marepvcl.b
    @24
    eqid
    marepvcl.v
    marepveval
    eqtrd
    stoic3
    @8
    @10
    @12
    @16
    @11
    @8
    @12
    cI
    cJ
    wceq
    #
    @15
    c.0
    cif
    @16
    @8
    cA
    cR
    c.1
    @15
    cI
    cJ
    cN
    c.0
    marepvcl.a
    @15
    eqid
    mulmarep1el.0
    @4
    @0
    @20
    @7
    @1
    @2
    @20
    @3
    @21
    3ad2ant1
    3ad2ant2
    @0
    @4
    @7
    simp1
    @0
    @4
    @5
    @6
    simp3l
    @0
    @4
    @5
    @6
    simp3r
    ma1repvcl.1
    mat1ov
    @8
    @26
    @14
    @15
    c.0
    @26
    @14
    wb
    @8
    cI
    cJ
    eqcom
    a1i
    ifbid
    eqtrd
    ifeq2d
    eqtrd
end
