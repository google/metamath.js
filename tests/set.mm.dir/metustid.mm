include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "wrel.mm"
include "relres.mm"
include "a1i.mm"
include "cv.mm"
include "cop.mm"
include "ccnv.mm"
include "cc0.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "wceq.mm"
include "crp.mm"
include "wbr.mm"
include "vex.mm"
include "brres.mm"
include "df-br.mm"
include "ideq.mm"
include "anbi1i.mm"
include "3bitr3i.mm"
include "biimpi.mm"
include "ad2antlr.mm"
include "simpld.mm"
include "df-ov.mm"
include "opeq2.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "syl.mm"
include "simplll.mm"
include "simprd.mm"
include "psmet0.mm"
include "syl2anc.mm"
include "eqtr3d.mm"
include "cxr.mm"
include "clt.mm"
include "0xr.mm"
include "rpxr.mm"
include "rpgt0.mm"
include "lbico1.mm"
include "syl3anc.mm"
include "adantl.mm"
include "eqeltrd.mm"
include "wfun.mm"
include "cdm.mm"
include "wb.mm"
include "cxp.mm"
include "wf.mm"
include "psmetf.mm"
include "ffun.mm"
include "ad3antrrr.mm"
include "eqeltrrd.mm"
include "opelxpi.mm"
include "fdm.mm"
include "eleqtrrd.mm"
include "fvimacnv.mm"
include "mpbid.mm"
include "adantr.mm"
include "simpr.mm"
include "wrex.mm"
include "simplr.mm"
include "metustel.mm"
include "ad2antrr.mm"
include "r19.29a.mm"
include "ex.mm"
include "relssdv.mm"

theorem metustid
  let cA: class A
  let cD: class D
  let cF: class F
  let cX: class X
  let va: setvar a
  let cB: class B
  let vb: setvar b
  let vp: setvar p
  let vq: setvar q
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume metust.1: |- F = ran ( a e. RR+ |-> ( `' D " ( 0 [,) a ) ) )

  disjoint D a
  disjoint X a
  disjoint A a
  disjoint F a
  disjoint B a
  disjoint a b
  disjoint A b
  disjoint B b
  disjoint D b
  disjoint F b
  disjoint X b
  disjoint a p
  disjoint a q
  disjoint b p
  disjoint b q
  disjoint p q
  disjoint A p
  disjoint A q
  disjoint a x
  disjoint p x
  disjoint D p
  disjoint q x
  disjoint D q
  disjoint D x
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint p y
  disjoint p z
  disjoint F p
  disjoint q y
  disjoint q z
  disjoint F q
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint X p
  disjoint X q
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ( D e. ( PsMet ` X ) /\ A e. F ) -> ( _I |` X ) C_ A )

  proof
    cD
    cX
    cpsmet
    cfv
    wcel
    #
    cA
    cF
    wcel
    #
    wa
    #
    vp
    vq
    cid
    cX
    cres
    #
    cA
    @3
    wrel
    @2
    cid
    cX
    relres
    a1i
    @2
    vp
    cv
    #
    vq
    cv
    #
    cop
    #
    @3
    wcel
    #
    @6
    cA
    wcel
    #
    @2
    @7
    wa
    #
    cA
    cD
    ccnv
    cc0
    va
    cv
    #
    cico
    co
    #
    cima
    #
    wceq
    #
    @8
    va
    crp
    @9
    @10
    crp
    wcel
    #
    wa
    #
    @13
    wa
    @6
    @12
    cA
    @15
    @6
    @12
    wcel
    #
    @13
    @15
    @6
    cD
    cfv
    #
    @11
    wcel
    #
    @16
    @15
    @17
    cc0
    @11
    @15
    @4
    @4
    cD
    co
    #
    @17
    cc0
    @15
    @4
    @5
    wceq
    #
    @19
    @17
    wceq
    @15
    @20
    @4
    cX
    wcel
    #
    @7
    @20
    @21
    wa
    #
    @2
    @14
    @7
    @22
    @4
    @5
    @3
    wbr
    @4
    @5
    cid
    wbr
    #
    @21
    wa
    @7
    @22
    @4
    @5
    cid
    cX
    vq
    vex
    #
    brres
    @4
    @5
    @3
    df-br
    @23
    @20
    @21
    @4
    @5
    @24
    ideq
    anbi1i
    3bitr3i
    biimpi
    ad2antlr
    #
    simpld
    #
    @20
    @19
    @4
    @4
    cop
    #
    cD
    cfv
    @17
    @4
    @4
    cD
    df-ov
    @20
    @27
    @6
    cD
    @4
    @5
    @4
    opeq2
    fveq2d
    syl5eq
    syl
    @15
    @0
    @21
    @19
    cc0
    wceq
    @0
    @1
    @7
    @14
    simplll
    @15
    @20
    @21
    @25
    simprd
    #
    @4
    cD
    cX
    psmet0
    syl2anc
    eqtr3d
    @14
    cc0
    @11
    wcel
    #
    @9
    @14
    cc0
    cxr
    wcel
    #
    @10
    cxr
    wcel
    cc0
    @10
    clt
    wbr
    @29
    @30
    @14
    0xr
    a1i
    @10
    rpxr
    @10
    rpgt0
    cc0
    @10
    lbico1
    syl3anc
    adantl
    eqeltrd
    @15
    cD
    wfun
    #
    @6
    cD
    cdm
    #
    wcel
    @18
    @16
    wb
    @0
    @31
    @1
    @7
    @14
    @0
    cX
    cX
    cxp
    #
    cxr
    cD
    wf
    #
    @31
    cD
    cX
    psmetf
    #
    @33
    cxr
    cD
    ffun
    syl
    ad3antrrr
    @15
    @6
    @33
    @32
    @15
    @21
    @5
    cX
    wcel
    @6
    @33
    wcel
    @28
    @15
    @4
    @5
    cX
    @26
    @28
    eqeltrrd
    @4
    @5
    cX
    cX
    opelxpi
    syl2anc
    @0
    @32
    @33
    wceq
    #
    @1
    @7
    @14
    @0
    @34
    @36
    @35
    @33
    cxr
    cD
    fdm
    syl
    ad3antrrr
    eleqtrrd
    @6
    @11
    cD
    fvimacnv
    syl2anc
    mpbid
    adantr
    @15
    @13
    simpr
    eleqtrrd
    @9
    @1
    @13
    va
    crp
    wrex
    #
    @0
    @1
    @7
    simplr
    @0
    @1
    @37
    wb
    @1
    @7
    cA
    cD
    cF
    cX
    va
    metust.1
    metustel
    ad2antrr
    mpbid
    r19.29a
    ex
    relssdv
end
