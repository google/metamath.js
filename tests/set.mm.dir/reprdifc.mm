include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "csu.mm"
include "wceq.mm"
include "cmap.mm"
include "cdif.mm"
include "crab.mm"
include "wcel.mm"
include "wn.mm"
include "crepr.mm"
include "ciun.mm"
include "nfv.mm"
include "nfrab1.mm"
include "nfcv.mm"
include "wa.mm"
include "wrex.mm"
include "nn0zd.mm"
include "reprval.mm"
include "eleq2d.mm"
include "rabid.mm"
include "syl6bb.mm"
include "anbi1d.mm"
include "wb.mm"
include "eldif.mm"
include "anbi1i.mm"
include "an32.mm"
include "bitri.mm"
include "a1i.mm"
include "bitr4d.mm"
include "wral.mm"
include "wf.mm"
include "cvv.mm"
include "cn.mm"
include "nnex.mm"
include "ssexd.mm"
include "ovexd.mm"
include "elmapg.mm"
include "syl2anc.mm"
include "adantr.mm"
include "wfn.mm"
include "wss.mm"
include "cz.mm"
include "cn0.mm"
include "simpr.mm"
include "reprf.mm"
include "ffn.mm"
include "syl.mm"
include "biantrurd.mm"
include "ffnfv.mm"
include "syl6rbbr.mm"
include "bitrd.mm"
include "notbid.mm"
include "rexnal.mm"
include "syl6bbr.mm"
include "pm5.32da.mm"
include "bitr3d.mm"
include "fveq1.mm"
include "eleq1d.mm"
include "elrab.mm"
include "rexbii.mm"
include "r19.42v.mm"
include "eliun.mm"
include "3bitr4g.mm"
include "eqrd.mm"
include "difeq12d.mm"
include "difrab2.mm"
include "syl6eq.mm"
include "iuneq2d.mm"
include "3eqtr4d.mm"

theorem reprdifc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cM: class M
  let vc: setvar c
  let vd: setvar d
  let va: setvar a
  assume reprdifc.c: |- C = { c e. ( A ( repr ` S ) M ) | -. ( c ` x ) e. B }
  assume reprdifc.a: |- ( ph -> A C_ NN )
  assume reprdifc.b: |- ( ph -> B C_ NN )
  assume reprdifc.m: |- ( ph -> M e. NN0 )
  assume reprdifc.s: |- ( ph -> S e. NN0 )

  disjoint A c
  disjoint A x
  disjoint c x
  disjoint B c
  disjoint B x
  disjoint M c
  disjoint M x
  disjoint S c
  disjoint S x
  disjoint ph x
  disjoint A d
  disjoint c d
  disjoint d x
  disjoint B d
  disjoint M d
  disjoint S a
  disjoint S d
  disjoint a c
  disjoint a d
  disjoint a x
  disjoint d ph
  assert |- ( ph -> ( ( A ( repr ` S ) M ) \ ( B ( repr ` S ) M ) ) = U_ x e. ( 0 ..^ S ) C )

  proof
    wph
    cc0
    cS
    cfzo
    co
    #
    va
    cv
    vd
    cv
    #
    cfv
    va
    csu
    cM
    wceq
    #
    vd
    cA
    @0
    cmap
    co
    #
    cB
    @0
    cmap
    co
    #
    cdif
    #
    crab
    #
    vx
    @0
    vx
    cv
    #
    vc
    cv
    #
    cfv
    #
    cB
    wcel
    #
    wn
    #
    vc
    cA
    cM
    cS
    crepr
    cfv
    #
    co
    #
    crab
    #
    ciun
    #
    @13
    cB
    cM
    @12
    co
    #
    cdif
    #
    vx
    @0
    cC
    ciun
    wph
    vd
    @6
    @15
    wph
    vd
    nfv
    @2
    vd
    @5
    nfrab1
    vd
    @15
    nfcv
    wph
    @1
    @5
    wcel
    #
    @2
    wa
    #
    @1
    @14
    wcel
    #
    vx
    @0
    wrex
    #
    @1
    @6
    wcel
    @1
    @15
    wcel
    wph
    @19
    @1
    @13
    wcel
    #
    @7
    @1
    cfv
    #
    cB
    wcel
    #
    wn
    #
    vx
    @0
    wrex
    #
    wa
    #
    @21
    wph
    @22
    @1
    @4
    wcel
    #
    wn
    #
    wa
    #
    @19
    @27
    wph
    @30
    @1
    @3
    wcel
    #
    @2
    wa
    #
    @29
    wa
    #
    @19
    wph
    @22
    @32
    @29
    wph
    @22
    @1
    @2
    vd
    @3
    crab
    #
    wcel
    @32
    wph
    @13
    @34
    @1
    wph
    cA
    cS
    cM
    va
    vd
    reprdifc.a
    wph
    cM
    reprdifc.m
    nn0zd
    #
    reprdifc.s
    reprval
    #
    eleq2d
    @2
    vd
    @3
    rabid
    syl6bb
    anbi1d
    @19
    @33
    wb
    wph
    @19
    @31
    @29
    wa
    #
    @2
    wa
    @33
    @18
    @37
    @2
    @1
    @3
    @4
    eldif
    anbi1i
    @31
    @29
    @2
    an32
    bitri
    a1i
    bitr4d
    wph
    @22
    @29
    @26
    wph
    @22
    wa
    #
    @29
    @24
    vx
    @0
    wral
    #
    wn
    @26
    @38
    @28
    @39
    @38
    @28
    @0
    cB
    @1
    wf
    #
    @39
    wph
    @28
    @40
    wb
    #
    @22
    wph
    cB
    cvv
    wcel
    @0
    cvv
    wcel
    @41
    wph
    cB
    cn
    cvv
    cn
    cvv
    wcel
    wph
    nnex
    a1i
    reprdifc.b
    ssexd
    wph
    cc0
    cS
    cfzo
    ovexd
    cB
    @0
    @1
    cvv
    cvv
    elmapg
    syl2anc
    adantr
    @38
    @39
    @1
    @0
    wfn
    #
    @39
    wa
    @40
    @38
    @42
    @39
    @38
    @0
    cA
    @1
    wf
    @42
    @38
    cA
    @1
    cS
    cM
    wph
    cA
    cn
    wss
    @22
    reprdifc.a
    adantr
    wph
    cM
    cz
    wcel
    @22
    @35
    adantr
    wph
    cS
    cn0
    wcel
    @22
    reprdifc.s
    adantr
    wph
    @22
    simpr
    reprf
    @0
    cA
    @1
    ffn
    syl
    biantrurd
    vx
    @0
    cB
    @1
    ffnfv
    syl6rbbr
    bitrd
    notbid
    @24
    vx
    @0
    rexnal
    syl6bbr
    pm5.32da
    bitr3d
    @21
    @22
    @25
    wa
    #
    vx
    @0
    wrex
    @27
    @20
    @43
    vx
    @0
    @11
    @25
    vc
    @1
    @13
    @8
    @1
    wceq
    #
    @10
    @24
    @44
    @9
    @23
    cB
    @7
    @8
    @1
    fveq1
    eleq1d
    notbid
    elrab
    rexbii
    @22
    @25
    vx
    @0
    r19.42v
    bitri
    syl6bbr
    @2
    vd
    @5
    rabid
    vx
    @1
    @0
    @14
    eliun
    3bitr4g
    eqrd
    wph
    @17
    @34
    @2
    vd
    @4
    crab
    #
    cdif
    @6
    wph
    @13
    @34
    @16
    @45
    @36
    wph
    cB
    cS
    cM
    va
    vd
    reprdifc.b
    @35
    reprdifc.s
    reprval
    difeq12d
    @2
    vd
    @3
    @4
    difrab2
    syl6eq
    wph
    vx
    @0
    cC
    @14
    cC
    @14
    wceq
    wph
    reprdifc.c
    a1i
    iuneq2d
    3eqtr4d
end
