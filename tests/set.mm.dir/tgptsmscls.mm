include "ctsu.mm"
include "co.mm"
include "csn.mm"
include "ccl.mm"
include "cfv.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "c0g.mm"
include "cqg.mm"
include "cec.mm"
include "wbr.mm"
include "csubg.mm"
include "wer.mm"
include "ctgp.mm"
include "adantr.mm"
include "cgrp.mm"
include "tgpgrp.mm"
include "syl.mm"
include "eqid.mm"
include "0subg.mm"
include "clssubg.mm"
include "syl2anc.mm"
include "eqger.mm"
include "csg.mm"
include "ctps.mm"
include "tgptps.mm"
include "tsmscl.mm"
include "sselda.mm"
include "sseldd.mm"
include "cof.mm"
include "ccmn.mm"
include "wf.mm"
include "simpr.mm"
include "tsmssub.mm"
include "cmpt.mm"
include "cgsu.mm"
include "ffvelrnda.mm"
include "feqmptd.mm"
include "offval2.mm"
include "wceq.mm"
include "grpsubid.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "grpidcl.mm"
include "fmptd.mm"
include "cxp.mm"
include "cfsupp.mm"
include "fconstmpt.mm"
include "cvv.mm"
include "fvexd.mm"
include "fczfsuppd.mm"
include "syl5eqbrr.mm"
include "tsmsgsum.mm"
include "cmnd.mm"
include "cmnmnd.mm"
include "gsumz.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "3eqtrd.mm"
include "eleqtrd.mm"
include "cabl.mm"
include "wss.mm"
include "w3a.mm"
include "wb.mm"
include "isabl.mm"
include "sylanbrc.mm"
include "subgss.mm"
include "eqgabl.mm"
include "mpbir3and.mm"
include "ersym.mm"
include "wrel.mm"
include "releqg.mm"
include "relelec.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "snclseqg.mm"
include "ex.mm"
include "ssrdv.mm"
include "tsmscls.mm"
include "eqssd.mm"

theorem tgptsmscls
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cJ: class J
  let cV: class V
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume tgptsmscls.b: |- B = ( Base ` G )
  assume tgptsmscls.j: |- J = ( TopOpen ` G )
  assume tgptsmscls.1: |- ( ph -> G e. CMnd )
  assume tgptsmscls.2: |- ( ph -> G e. TopGrp )
  assume tgptsmscls.a: |- ( ph -> A e. V )
  assume tgptsmscls.f: |- ( ph -> F : A --> B )
  assume tgptsmscls.x: |- ( ph -> X e. ( G tsums F ) )


  assert |- ( ph -> ( G tsums F ) = ( ( cls ` J ) ` { X } ) )

  proof
    wph
    cG
    cF
    ctsu
    co
    #
    cX
    csn
    cJ
    ccl
    cfv
    #
    cfv
    #
    wph
    vx
    @0
    @2
    wph
    vx
    cv
    #
    @0
    wcel
    #
    @3
    @2
    wcel
    wph
    @4
    wa
    #
    @3
    cX
    cG
    cG
    c0g
    cfv
    #
    csn
    #
    @1
    cfv
    #
    cqg
    co
    #
    cec
    #
    @2
    @5
    cX
    @3
    @9
    wbr
    #
    @3
    @10
    wcel
    #
    @5
    @3
    cX
    @9
    cB
    @5
    @8
    cG
    csubg
    cfv
    #
    wcel
    #
    cB
    @9
    wer
    @5
    cG
    ctgp
    wcel
    #
    @7
    @13
    wcel
    #
    @14
    wph
    @15
    @4
    tgptsmscls.2
    adantr
    #
    @5
    cG
    cgrp
    wcel
    #
    @16
    @5
    @15
    @18
    @17
    cG
    tgpgrp
    syl
    #
    cG
    @6
    @6
    eqid
    #
    0subg
    syl
    @7
    cG
    cJ
    tgptsmscls.j
    clssubg
    syl2anc
    #
    @9
    cG
    cB
    @8
    tgptsmscls.b
    @9
    eqid
    #
    eqger
    syl
    @5
    @3
    cX
    @9
    wbr
    #
    @3
    cB
    wcel
    #
    cX
    cB
    wcel
    #
    cX
    @3
    cG
    csg
    cfv
    #
    co
    #
    @8
    wcel
    #
    wph
    @0
    cB
    @3
    wph
    cA
    cB
    cF
    cG
    cV
    tgptsmscls.b
    tgptsmscls.1
    wph
    @15
    cG
    ctps
    wcel
    #
    tgptsmscls.2
    cG
    tgptps
    #
    syl
    #
    tgptsmscls.a
    tgptsmscls.f
    tsmscl
    #
    sselda
    wph
    @25
    @4
    wph
    @0
    cB
    cX
    @32
    tgptsmscls.x
    sseldd
    adantr
    #
    @5
    @27
    cG
    cF
    cF
    @26
    cof
    co
    #
    ctsu
    co
    #
    @8
    @5
    cA
    cB
    cF
    cG
    cF
    @26
    cV
    cX
    @3
    tgptsmscls.b
    @26
    eqid
    #
    wph
    cG
    ccmn
    wcel
    #
    @4
    tgptsmscls.1
    adantr
    #
    @17
    wph
    cA
    cV
    wcel
    #
    @4
    tgptsmscls.a
    adantr
    #
    wph
    cA
    cB
    cF
    wf
    @4
    tgptsmscls.f
    adantr
    #
    @41
    wph
    cX
    @0
    wcel
    @4
    tgptsmscls.x
    adantr
    wph
    @4
    simpr
    tsmssub
    @5
    @35
    cG
    vk
    cA
    @6
    cmpt
    #
    ctsu
    co
    cG
    @42
    cgsu
    co
    #
    csn
    #
    @1
    cfv
    @8
    @5
    @34
    @42
    cG
    ctsu
    @5
    @34
    vk
    cA
    vk
    cv
    #
    cF
    cfv
    #
    @46
    @26
    co
    #
    cmpt
    @42
    @5
    vk
    cA
    @46
    @46
    @26
    cF
    cF
    cV
    cB
    cB
    @40
    @5
    cA
    cB
    @45
    cF
    @41
    ffvelrnda
    #
    @48
    @5
    vk
    cA
    cB
    cF
    @41
    feqmptd
    #
    @49
    offval2
    @5
    vk
    cA
    @47
    @6
    @5
    @45
    cA
    wcel
    #
    wa
    @18
    @46
    cB
    wcel
    @47
    @6
    wceq
    @5
    @18
    @50
    @19
    adantr
    @48
    cB
    cG
    @26
    @46
    @6
    tgptsmscls.b
    @20
    @36
    grpsubid
    syl2anc
    mpteq2dva
    eqtrd
    oveq2d
    @5
    cA
    cB
    @42
    cG
    cJ
    cV
    @6
    tgptsmscls.b
    @20
    @38
    @5
    @15
    @29
    @17
    @30
    syl
    @40
    @5
    vk
    cA
    @6
    cB
    @42
    @5
    @6
    cB
    wcel
    #
    @50
    @5
    @18
    @51
    @19
    cB
    cG
    @6
    tgptsmscls.b
    @20
    grpidcl
    syl
    adantr
    @42
    eqid
    fmptd
    @5
    @42
    cA
    @7
    cxp
    #
    @6
    cfsupp
    vk
    cA
    @6
    fconstmpt
    wph
    @52
    @6
    cfsupp
    wbr
    @4
    wph
    cA
    cV
    cvv
    @6
    tgptsmscls.a
    wph
    cG
    c0g
    fvexd
    fczfsuppd
    adantr
    syl5eqbrr
    tgptsmscls.j
    tsmsgsum
    @5
    @44
    @7
    @1
    @5
    @43
    @6
    @5
    cG
    cmnd
    wcel
    #
    @39
    @43
    @6
    wceq
    @5
    @37
    @53
    @38
    cG
    cmnmnd
    syl
    @40
    cA
    vk
    cG
    cV
    @6
    @20
    gsumz
    syl2anc
    sneqd
    fveq2d
    3eqtrd
    eleqtrd
    @5
    cG
    cabl
    wcel
    #
    @8
    cB
    wss
    #
    @23
    @24
    @25
    @28
    w3a
    wb
    @5
    @18
    @37
    @54
    @19
    @38
    cG
    isabl
    sylanbrc
    @5
    @14
    @55
    @21
    cB
    @8
    cG
    tgptsmscls.b
    subgss
    syl
    @3
    cX
    @9
    @8
    cG
    @26
    cB
    tgptsmscls.b
    @36
    @22
    eqgabl
    syl2anc
    mpbir3and
    ersym
    @9
    wrel
    @12
    @11
    wb
    @9
    @8
    cG
    @22
    releqg
    @3
    cX
    @9
    relelec
    ax-mp
    sylibr
    @5
    @15
    @25
    @10
    @2
    wceq
    @17
    @33
    cX
    @9
    @8
    cG
    cJ
    cB
    @6
    tgptsmscls.b
    tgptsmscls.j
    @20
    @22
    @8
    eqid
    snclseqg
    syl2anc
    eleqtrd
    ex
    ssrdv
    wph
    cA
    cB
    cF
    cG
    cJ
    cV
    cX
    tgptsmscls.b
    tgptsmscls.j
    tgptsmscls.1
    @31
    tgptsmscls.a
    tgptsmscls.f
    tgptsmscls.x
    tsmscls
    eqssd
end
