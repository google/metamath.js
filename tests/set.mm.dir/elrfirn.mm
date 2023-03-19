include "wcel.mm"
include "cpw.mm"
include "wf.mm"
include "wa.mm"
include "csn.mm"
include "crn.mm"
include "cun.mm"
include "cfi.mm"
include "cfv.mm"
include "cv.mm"
include "cint.mm"
include "cin.mm"
include "wceq.mm"
include "cfn.mm"
include "wrex.mm"
include "cima.mm"
include "ciin.mm"
include "wss.mm"
include "wb.mm"
include "frn.mm"
include "elrfi.mm"
include "sylan2.mm"
include "imassrn.mm"
include "cvv.mm"
include "pwexg.mm"
include "ssexg.mm"
include "syl2anr.mm"
include "elpw2g.mm"
include "syl.mm"
include "mpbiri.mm"
include "adantr.mm"
include "wfun.mm"
include "ffun.mm"
include "ad2antlr.mm"
include "inss2.mm"
include "sseli.mm"
include "adantl.mm"
include "imafi.mm"
include "syl2anc.mm"
include "elind.mm"
include "wfn.mm"
include "ffn.mm"
include "inss1.mm"
include "elpwid.mm"
include "fipreima.mm"
include "syl3anc.mm"
include "eqcom.mm"
include "rexbii.mm"
include "sylib.mm"
include "inteq.mm"
include "ineq2d.mm"
include "eqeq2d.mm"
include "rexxfrd.mm"
include "imaiinfv.mm"
include "eqcomd.mm"
include "rexbidva.mm"
include "3bitrd.mm"

theorem elrfirn
  let vy: setvar y
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cF: class F
  let cI: class I
  let cV: class V
  let vw: setvar w

  disjoint A v
  disjoint B v
  disjoint F v
  disjoint F y
  disjoint I v
  disjoint V v
  disjoint v y
  disjoint A w
  disjoint v w
  disjoint B w
  disjoint F w
  disjoint I w
  disjoint V w
  assert |- ( ( B e. V /\ F : I --> ~P B ) -> ( A e. ( fi ` ( { B } u. ran F ) ) <-> E. v e. ( ~P I i^i Fin ) A = ( B i^i |^|_ y e. v ( F ` y ) ) ) )

  proof
    cB
    cV
    wcel
    #
    cI
    cB
    cpw
    #
    cF
    wf
    #
    wa
    #
    cA
    cB
    csn
    cF
    crn
    #
    cun
    cfi
    cfv
    wcel
    #
    cA
    cB
    vw
    cv
    #
    cint
    #
    cin
    #
    wceq
    #
    vw
    @4
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    cA
    cB
    cF
    vv
    cv
    #
    cima
    #
    cint
    #
    cin
    #
    wceq
    #
    vv
    cI
    cpw
    #
    cfn
    cin
    #
    wrex
    cA
    cB
    vy
    @13
    vy
    cv
    cF
    cfv
    ciin
    #
    cin
    #
    wceq
    #
    vv
    @19
    wrex
    @2
    @0
    @4
    @1
    wss
    #
    @5
    @12
    wb
    cI
    @1
    cF
    frn
    #
    vw
    cA
    cB
    @4
    cV
    elrfi
    sylan2
    @3
    @9
    @17
    vw
    vv
    @14
    @11
    @19
    @3
    @13
    @19
    wcel
    #
    wa
    #
    @10
    cfn
    @14
    @3
    @14
    @10
    wcel
    #
    @25
    @3
    @27
    @14
    @4
    wss
    #
    cF
    @13
    imassrn
    @3
    @4
    cvv
    wcel
    #
    @27
    @28
    wb
    @2
    @23
    @1
    cvv
    wcel
    @29
    @0
    @24
    cB
    cV
    pwexg
    @4
    @1
    cvv
    ssexg
    syl2anr
    @14
    @4
    cvv
    elpw2g
    syl
    mpbiri
    adantr
    @26
    cF
    wfun
    #
    @13
    cfn
    wcel
    #
    @14
    cfn
    wcel
    @2
    @30
    @0
    @25
    cI
    @1
    cF
    ffun
    ad2antlr
    @25
    @31
    @3
    @19
    cfn
    @13
    @18
    cfn
    inss2
    sseli
    adantl
    cF
    @13
    imafi
    syl2anc
    elind
    @3
    @6
    @11
    wcel
    #
    wa
    #
    @14
    @6
    wceq
    #
    vv
    @19
    wrex
    #
    @6
    @14
    wceq
    #
    vv
    @19
    wrex
    @33
    cF
    cI
    wfn
    #
    @6
    @4
    wss
    #
    @6
    cfn
    wcel
    #
    @35
    @2
    @37
    @0
    @32
    cI
    @1
    cF
    ffn
    #
    ad2antlr
    @32
    @38
    @3
    @32
    @6
    @4
    @11
    @10
    @6
    @10
    cfn
    inss1
    sseli
    elpwid
    adantl
    @32
    @39
    @3
    @11
    cfn
    @6
    @10
    cfn
    inss2
    sseli
    adantl
    @6
    cI
    cF
    vv
    fipreima
    syl3anc
    @34
    @36
    vv
    @19
    @14
    @6
    eqcom
    rexbii
    sylib
    @36
    @9
    @17
    wb
    @3
    @36
    @8
    @16
    cA
    @36
    @7
    @15
    cB
    @6
    @14
    inteq
    ineq2d
    eqeq2d
    adantl
    rexxfrd
    @3
    @17
    @22
    vv
    @19
    @26
    @16
    @21
    cA
    @26
    @15
    @20
    cB
    @26
    @20
    @15
    @26
    @37
    @13
    cI
    wss
    #
    @20
    @15
    wceq
    @2
    @37
    @0
    @25
    @40
    ad2antlr
    @25
    @41
    @3
    @25
    @13
    cI
    @19
    @18
    @13
    @18
    cfn
    inss1
    sseli
    elpwid
    adantl
    vy
    cI
    @13
    cF
    imaiinfv
    syl2anc
    eqcomd
    ineq2d
    eqeq2d
    rexbidva
    3bitrd
end
