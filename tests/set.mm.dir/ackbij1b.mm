include "com.mm"
include "wcel.mm"
include "cpw.mm"
include "cima.mm"
include "ccrd.mm"
include "cfv.mm"
include "wpss.mm"
include "wn.mm"
include "wceq.mm"
include "wo.mm"
include "cen.mm"
include "wbr.mm"
include "cfn.mm"
include "cin.mm"
include "wss.mm"
include "cvv.mm"
include "ackbij2lem1.mm"
include "pwexg.mm"
include "wf1.mm"
include "ackbij1lem17.mm"
include "f1imaeng.mm"
include "mp3an1.mm"
include "syl2anc.mm"
include "nnfi.mm"
include "pwfi.mm"
include "sylib.mm"
include "ficardid.mm"
include "ensym.mm"
include "3syl.mm"
include "entr.mm"
include "csdm.mm"
include "wi.mm"
include "con0.mm"
include "onfin2.mm"
include "inss2.mm"
include "eqsstri.mm"
include "ficardom.mm"
include "syl.mm"
include "sseldi.mm"
include "php3.mm"
include "ex.mm"
include "sdomnen.mm"
include "syl6.mm"
include "mt2d.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "csuc.mm"
include "fvex.mm"
include "ackbij1lem3.mm"
include "elpwi.mm"
include "ackbij1lem12.mm"
include "syl2an.mm"
include "word.mm"
include "wb.mm"
include "ackbij1lem10.mm"
include "peano1.mm"
include "f0cli.mm"
include "nnord.mm"
include "ax-mp.mm"
include "ordsucsssuc.mm"
include "mp2an.mm"
include "csn.mm"
include "ackbij1lem14.mm"
include "ackbij1lem8.mm"
include "eqtr3d.mm"
include "adantr.mm"
include "sseqtrd.mm"
include "sucssel.mm"
include "mpsyl.mm"
include "ralrimiva.mm"
include "wfun.mm"
include "cdm.mm"
include "f1fun.mm"
include "f1dm.mm"
include "syl6sseqr.mm"
include "funimass4.mm"
include "sylancr.mm"
include "mpbird.mm"
include "sspss.mm"
include "orel1.mm"
include "sylc.mm"

theorem ackbij1b
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cG: class G
  let cH: class H
  let cB: class B
  assume ackbij.f: |- F = ( x e. ( ~P _om i^i Fin ) |-> ( card ` U_ y e. x ( { y } X. ~P y ) ) )

  disjoint F x
  disjoint F y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G x
  disjoint G y
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint H x
  disjoint H y
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B x
  disjoint B y
  assert |- ( A e. _om -> ( F " ~P A ) = ( card ` ~P A ) )

  proof
    cA
    com
    wcel
    #
    cF
    cA
    cpw
    #
    cima
    #
    @1
    ccrd
    cfv
    #
    wpss
    #
    wn
    @4
    @2
    @3
    wceq
    #
    wo
    #
    @5
    @0
    @4
    @2
    @3
    cen
    wbr
    #
    @0
    @2
    @1
    cen
    wbr
    #
    @1
    @3
    cen
    wbr
    #
    @7
    @0
    @1
    com
    cpw
    cfn
    cin
    #
    wss
    #
    @1
    cvv
    wcel
    #
    @8
    cA
    ackbij2lem1
    #
    cA
    com
    pwexg
    @10
    com
    cF
    wf1
    #
    @11
    @12
    @8
    vx
    vy
    cF
    ackbij.f
    ackbij1lem17
    #
    @10
    com
    @1
    cF
    cvv
    f1imaeng
    mp3an1
    syl2anc
    @0
    @1
    cfn
    wcel
    #
    @3
    @1
    cen
    wbr
    @9
    @0
    cA
    cfn
    wcel
    @16
    cA
    nnfi
    cA
    pwfi
    sylib
    #
    @1
    ficardid
    @3
    @1
    ensym
    3syl
    @2
    @1
    @3
    entr
    syl2anc
    @0
    @4
    @2
    @3
    csdm
    wbr
    #
    @7
    wn
    @0
    @3
    cfn
    wcel
    #
    @4
    @18
    wi
    @0
    com
    cfn
    @3
    com
    con0
    cfn
    cin
    cfn
    onfin2
    con0
    cfn
    inss2
    eqsstri
    @0
    @16
    @3
    com
    wcel
    @17
    @1
    ficardom
    syl
    sseldi
    @19
    @4
    @18
    @3
    @2
    php3
    ex
    syl
    @2
    @3
    sdomnen
    syl6
    mt2d
    @0
    @2
    @3
    wss
    #
    @6
    @0
    @20
    va
    cv
    #
    cF
    cfv
    #
    @3
    wcel
    #
    va
    @1
    wral
    #
    @0
    @23
    va
    @1
    @22
    cvv
    wcel
    @0
    @21
    @1
    wcel
    #
    wa
    #
    @22
    csuc
    #
    @3
    wss
    @23
    @21
    cF
    fvex
    @26
    @27
    cA
    cF
    cfv
    #
    csuc
    #
    @3
    @26
    @22
    @28
    wss
    #
    @27
    @29
    wss
    #
    @0
    cA
    @10
    wcel
    @21
    cA
    wss
    @30
    @25
    cA
    ackbij1lem3
    @21
    cA
    elpwi
    vx
    vy
    @21
    cA
    cF
    ackbij.f
    ackbij1lem12
    syl2an
    @22
    word
    #
    @28
    word
    #
    @30
    @31
    wb
    @22
    com
    wcel
    @32
    @10
    com
    @21
    cF
    vx
    vy
    cF
    ackbij.f
    ackbij1lem10
    #
    peano1
    f0cli
    @22
    nnord
    ax-mp
    @28
    com
    wcel
    @33
    @10
    com
    cA
    cF
    @34
    peano1
    f0cli
    @28
    nnord
    ax-mp
    @22
    @28
    ordsucsssuc
    mp2an
    sylib
    @0
    @29
    @3
    wceq
    @25
    @0
    cA
    csn
    cF
    cfv
    @29
    @3
    vx
    vy
    cA
    cF
    ackbij.f
    ackbij1lem14
    vx
    vy
    cA
    cF
    ackbij.f
    ackbij1lem8
    eqtr3d
    adantr
    sseqtrd
    @22
    @3
    cvv
    sucssel
    mpsyl
    ralrimiva
    @0
    cF
    wfun
    #
    @1
    cF
    cdm
    #
    wss
    @20
    @24
    wb
    @14
    @35
    @15
    @10
    com
    cF
    f1fun
    ax-mp
    @0
    @1
    @10
    @36
    @13
    @14
    @36
    @10
    wceq
    @15
    @10
    com
    cF
    f1dm
    ax-mp
    syl6sseqr
    va
    @1
    @3
    cF
    funimass4
    sylancr
    mpbird
    @2
    @3
    sspss
    sylib
    @4
    @5
    orel1
    sylc
end
