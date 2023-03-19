include "wfn.mm"
include "wa.mm"
include "wss.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "csupp.mm"
include "co.mm"
include "wne.mm"
include "cdm.mm"
include "crab.mm"
include "wb.mm"
include "fndm.mm"
include "eleq2d.mm"
include "ad2antrr.mm"
include "weq.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl6bi.mm"
include "com23.mm"
include "imp31.mm"
include "necon3d.mm"
include "ss2rabdv.mm"
include "simpr1.mm"
include "ad2antlr.mm"
include "3sstr4d.mm"
include "adantr.mm"
include "rabss2.mm"
include "syl.mm"
include "sstrd.mm"
include "wfun.mm"
include "cvv.mm"
include "fnfun.mm"
include "simpl.mm"
include "ssexg.mm"
include "3adant3.mm"
include "fnex.mm"
include "syl2an.mm"
include "simpr3.mm"
include "suppval1.mm"
include "syl3anc.mm"
include "simpr.mm"
include "simp2.mm"
include "sseq12d.mm"
include "mpbird.mm"
include "ex.mm"

theorem suppfnss
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vy: setvar y

  disjoint A x
  disjoint F x
  disjoint G x
  disjoint Z x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint F y
  disjoint G y
  disjoint V y
  disjoint W y
  disjoint Z y
  assert |- ( ( ( F Fn A /\ G Fn B ) /\ ( A C_ B /\ B e. V /\ Z e. W ) ) -> ( A. x e. A ( ( G ` x ) = Z -> ( F ` x ) = Z ) -> ( F supp Z ) C_ ( G supp Z ) ) )

  proof
    cF
    cA
    wfn
    #
    cG
    cB
    wfn
    #
    wa
    #
    cA
    cB
    wss
    #
    cB
    cV
    wcel
    #
    cZ
    cW
    wcel
    #
    w3a
    #
    wa
    #
    vx
    cv
    #
    cG
    cfv
    #
    cZ
    wceq
    #
    @8
    cF
    cfv
    #
    cZ
    wceq
    #
    wi
    #
    vx
    cA
    wral
    #
    cF
    cZ
    csupp
    co
    #
    cG
    cZ
    csupp
    co
    #
    wss
    #
    @7
    @14
    wa
    #
    @17
    vy
    cv
    #
    cF
    cfv
    #
    cZ
    wne
    #
    vy
    cF
    cdm
    #
    crab
    #
    @19
    cG
    cfv
    #
    cZ
    wne
    #
    vy
    cG
    cdm
    #
    crab
    #
    wss
    #
    @18
    @23
    @25
    vy
    @22
    crab
    #
    @27
    @18
    @21
    @25
    vy
    @22
    @18
    @19
    @22
    wcel
    #
    wa
    @24
    cZ
    @20
    cZ
    @7
    @14
    @30
    @24
    cZ
    wceq
    #
    @20
    cZ
    wceq
    #
    wi
    #
    @7
    @30
    @14
    @33
    @7
    @30
    @19
    cA
    wcel
    #
    @14
    @33
    wi
    @0
    @30
    @34
    wb
    @1
    @6
    @0
    @22
    cA
    @19
    cA
    cF
    fndm
    #
    eleq2d
    ad2antrr
    @13
    @33
    vx
    @19
    cA
    vx
    vy
    weq
    #
    @10
    @31
    @12
    @32
    @36
    @9
    @24
    cZ
    @8
    @19
    cG
    fveq2
    eqeq1d
    @36
    @11
    @20
    cZ
    @8
    @19
    cF
    fveq2
    eqeq1d
    imbi12d
    rspcv
    syl6bi
    com23
    imp31
    necon3d
    ss2rabdv
    @18
    @22
    @26
    wss
    #
    @29
    @27
    wss
    @7
    @37
    @14
    @7
    cA
    cB
    @22
    @26
    @2
    @3
    @4
    @5
    simpr1
    @0
    @22
    cA
    wceq
    @1
    @6
    @35
    ad2antrr
    @1
    @26
    cB
    wceq
    @0
    @6
    cB
    cG
    fndm
    ad2antlr
    3sstr4d
    adantr
    @25
    vy
    @22
    @26
    rabss2
    syl
    sstrd
    @7
    @17
    @28
    wb
    @14
    @7
    @15
    @23
    @16
    @27
    @7
    cF
    wfun
    #
    cF
    cvv
    wcel
    #
    @5
    @15
    @23
    wceq
    @0
    @38
    @1
    @6
    cA
    cF
    fnfun
    ad2antrr
    @2
    @0
    cA
    cvv
    wcel
    #
    @39
    @6
    @0
    @1
    simpl
    @3
    @4
    @40
    @5
    cA
    cB
    cV
    ssexg
    3adant3
    cA
    cvv
    cF
    fnex
    syl2an
    @2
    @3
    @4
    @5
    simpr3
    #
    vy
    cvv
    cW
    cF
    cZ
    suppval1
    syl3anc
    @7
    cG
    wfun
    #
    cG
    cvv
    wcel
    #
    @5
    @16
    @27
    wceq
    @1
    @42
    @0
    @6
    cB
    cG
    fnfun
    ad2antlr
    @2
    @1
    @4
    @43
    @6
    @0
    @1
    simpr
    @3
    @4
    @5
    simp2
    cB
    cV
    cG
    fnex
    syl2an
    @41
    vy
    cvv
    cW
    cG
    cZ
    suppval1
    syl3anc
    sseq12d
    adantr
    mpbird
    ex
end
