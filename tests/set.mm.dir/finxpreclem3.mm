include "com.mm"
include "wcel.mm"
include "c2o.mm"
include "wss.mm"
include "wa.mm"
include "cvv.mm"
include "cxp.mm"
include "cop.mm"
include "cfv.mm"
include "co.mm"
include "cuni.mm"
include "c1st.mm"
include "df-ov.mm"
include "cv.mm"
include "c1o.mm"
include "wceq.mm"
include "c0.mm"
include "cif.mm"
include "cmpt2.mm"
include "a1i.mm"
include "eqeq1.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "wb.mm"
include "adantl.mm"
include "unieq.mm"
include "adantr.mm"
include "fveq2.mm"
include "opeq12d.mm"
include "opeq12.mm"
include "ifbieq12d.mm"
include "ifbieq2d.mm"
include "wpss.mm"
include "wne.mm"
include "csuc.mm"
include "sssucid.mm"
include "df-2o.mm"
include "sseqtr4i.mm"
include "1on.mm"
include "sucneqoni.mm"
include "necomi.mm"
include "df-pss.mm"
include "mpbir2an.mm"
include "ssnpss.mm"
include "mt2.mm"
include "sseq2.mm"
include "mtbiri.mm"
include "con2i.mm"
include "intnanrd.mm"
include "iffalsed.mm"
include "iftrue.mm"
include "sylan9eq.mm"
include "sylan9eqr.mm"
include "adantlll.mm"
include "simpll.mm"
include "elex.mm"
include "opex.mm"
include "ovmpt2d.mm"
include "syl5reqr.mm"

theorem finxpreclem3
  let vx: setvar x
  let cU: class U
  let vn: setvar n
  let cF: class F
  let cN: class N
  let cX: class X
  assume finxpreclem3.1: |- F = ( n e. _om , x e. _V |-> if ( ( n = 1o /\ x e. U ) , (/) , if ( x e. ( _V X. U ) , <. U. n , ( 1st ` x ) >. , <. n , x >. ) ) )

  disjoint N n
  disjoint N x
  disjoint n x
  disjoint U n
  disjoint U x
  disjoint X n
  disjoint X x
  assert |- ( ( ( N e. _om /\ 2o C_ N ) /\ X e. ( _V X. U ) ) -> <. U. N , ( 1st ` X ) >. = ( F ` <. N , X >. ) )

  proof
    cN
    com
    wcel
    #
    c2o
    cN
    wss
    #
    wa
    #
    cX
    cvv
    cU
    cxp
    #
    wcel
    #
    wa
    #
    cN
    cX
    cop
    #
    cF
    cfv
    cN
    cX
    cF
    co
    cN
    cuni
    #
    cX
    c1st
    cfv
    #
    cop
    #
    cN
    cX
    cF
    df-ov
    @5
    vn
    vx
    cN
    cX
    com
    cvv
    vn
    cv
    #
    c1o
    wceq
    #
    vx
    cv
    #
    cU
    wcel
    #
    wa
    #
    c0
    @12
    @3
    wcel
    #
    @10
    cuni
    #
    @12
    c1st
    cfv
    #
    cop
    #
    @10
    @12
    cop
    #
    cif
    #
    cif
    #
    @9
    cF
    cvv
    cF
    vn
    vx
    com
    cvv
    @21
    cmpt2
    wceq
    @5
    finxpreclem3.1
    a1i
    @1
    @4
    @10
    cN
    wceq
    #
    @12
    cX
    wceq
    #
    wa
    #
    @21
    @9
    wceq
    @0
    @24
    @1
    @4
    wa
    @21
    cN
    c1o
    wceq
    #
    cX
    cU
    wcel
    #
    wa
    #
    c0
    @4
    @9
    @6
    cif
    #
    cif
    #
    @9
    @24
    @14
    @27
    @20
    @28
    c0
    @22
    @11
    @25
    @23
    @13
    @26
    @10
    cN
    c1o
    eqeq1
    @12
    cX
    cU
    eleq1
    bi2anan9
    @24
    @15
    @4
    @18
    @19
    @9
    @6
    @23
    @15
    @4
    wb
    @22
    @12
    cX
    @3
    eleq1
    adantl
    @24
    @16
    @7
    @17
    @8
    @22
    @16
    @7
    wceq
    @23
    @10
    cN
    unieq
    adantr
    @23
    @17
    @8
    wceq
    @22
    @12
    cX
    c1st
    fveq2
    adantl
    opeq12d
    @10
    @12
    cN
    cX
    opeq12
    ifbieq12d
    ifbieq2d
    @1
    @4
    @29
    @28
    @9
    @1
    @27
    c0
    @28
    @1
    @25
    @26
    @25
    @1
    @25
    @1
    c2o
    c1o
    wss
    #
    @30
    c1o
    c2o
    wpss
    #
    @31
    c1o
    c2o
    wss
    c1o
    c2o
    wne
    c1o
    c1o
    csuc
    c2o
    c1o
    sssucid
    df-2o
    sseqtr4i
    c2o
    c1o
    c2o
    c1o
    df-2o
    1on
    sucneqoni
    necomi
    c1o
    c2o
    df-pss
    mpbir2an
    c2o
    c1o
    ssnpss
    mt2
    cN
    c1o
    c2o
    sseq2
    mtbiri
    con2i
    intnanrd
    iffalsed
    @4
    @9
    @6
    iftrue
    sylan9eq
    sylan9eqr
    adantlll
    @0
    @1
    @4
    simpll
    @4
    cX
    cvv
    wcel
    @2
    cX
    @3
    elex
    adantl
    @9
    cvv
    wcel
    @5
    @7
    @8
    opex
    a1i
    ovmpt2d
    syl5reqr
end
