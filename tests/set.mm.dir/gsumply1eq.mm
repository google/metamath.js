include "wceq.mm"
include "cv.mm"
include "cco1.mm"
include "cfv.mm"
include "cn0.mm"
include "wral.mm"
include "crg.mm"
include "wcel.mm"
include "cbs.mm"
include "wb.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "eqid.mm"
include "gsumsmonply1.mm"
include "eqeltrd.mm"
include "w3a.mm"
include "ply1coe1eq.mm"
include "bicomd.mm"
include "syl3anc.mm"
include "wa.mm"
include "csb.mm"
include "adantr.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfov.mm"
include "csbeq1a.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "cbvmpt.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "nfv.mm"
include "nfel1.mm"
include "eleq1d.mm"
include "cbvral.mm"
include "sylib.mm"
include "cfsupp.mm"
include "wbr.mm"
include "syl5eqbrr.mm"
include "simpr.mm"
include "gsummoncoe1.mm"
include "csbco.mm"
include "csbid.mm"
include "eqtri.mm"
include "eqtrd.mm"
include "a1i.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "ralbidva.mm"
include "bitrd.mm"

theorem gsumply1eq
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let vk: setvar k
  let c.ex: class .^
  let c.as: class .*
  let cK: class K
  let cO: class O
  let cX: class X
  let c.0: class .0.
  let vl: setvar l
  assume gsumply1eq.p: |- P = ( Poly1 ` R )
  assume gsumply1eq.x: |- X = ( var1 ` R )
  assume gsumply1eq.e: |- .^ = ( .g ` ( mulGrp ` P ) )
  assume gsumply1eq.r: |- ( ph -> R e. Ring )
  assume gsumply1eq.k: |- K = ( Base ` R )
  assume gsumply1eq.m: |- .* = ( .s ` P )
  assume gsumply1eq.0: |- .0. = ( 0g ` R )
  assume gsumply1eq.a: |- ( ph -> A. k e. NN0 A e. K )
  assume gsumply1eq.f1: |- ( ph -> ( k e. NN0 |-> A ) finSupp .0. )
  assume gsumply1eq.b: |- ( ph -> A. k e. NN0 B e. K )
  assume gsumply1eq.f2: |- ( ph -> ( k e. NN0 |-> B ) finSupp .0. )
  assume gsumply1eq.o: |- ( ph -> O = ( P gsum ( k e. NN0 |-> ( A .* ( k .^ X ) ) ) ) )
  assume gsumply1eq.q: |- ( ph -> Q = ( P gsum ( k e. NN0 |-> ( B .* ( k .^ X ) ) ) ) )

  disjoint K k
  disjoint O k
  disjoint P k
  disjoint Q k
  disjoint R k
  disjoint X k
  disjoint k ph
  disjoint .0. k
  disjoint .* k
  disjoint .^ k
  disjoint A l
  disjoint B l
  disjoint K l
  disjoint k l
  disjoint P l
  disjoint R l
  disjoint X l
  disjoint l ph
  disjoint .0. l
  disjoint .* l
  disjoint .^ l
  assert |- ( ph -> ( O = Q <-> A. k e. NN0 A = B ) )

  proof
    wph
    cO
    cQ
    wceq
    #
    vk
    cv
    #
    cO
    cco1
    cfv
    #
    cfv
    #
    @1
    cQ
    cco1
    cfv
    #
    cfv
    #
    wceq
    #
    vk
    cn0
    wral
    #
    cA
    cB
    wceq
    #
    vk
    cn0
    wral
    wph
    cR
    crg
    wcel
    #
    cO
    cP
    cbs
    cfv
    #
    wcel
    #
    cQ
    @10
    wcel
    #
    @0
    @7
    wb
    gsumply1eq.r
    wph
    cO
    cP
    vk
    cn0
    cA
    @1
    cX
    c.ex
    co
    #
    c.as
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @10
    gsumply1eq.o
    wph
    cA
    @10
    cP
    cR
    vk
    c.ex
    c.as
    cK
    cX
    c.0
    gsumply1eq.p
    @10
    eqid
    #
    gsumply1eq.x
    gsumply1eq.e
    gsumply1eq.r
    gsumply1eq.k
    gsumply1eq.m
    gsumply1eq.0
    gsumply1eq.a
    gsumply1eq.f1
    gsumsmonply1
    eqeltrd
    wph
    cQ
    cP
    vk
    cn0
    cB
    @13
    c.as
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @10
    gsumply1eq.q
    wph
    cB
    @10
    cP
    cR
    vk
    c.ex
    c.as
    cK
    cX
    c.0
    gsumply1eq.p
    @17
    gsumply1eq.x
    gsumply1eq.e
    gsumply1eq.r
    gsumply1eq.k
    gsumply1eq.m
    gsumply1eq.0
    gsumply1eq.b
    gsumply1eq.f2
    gsumsmonply1
    eqeltrd
    @9
    @11
    @12
    w3a
    @7
    @0
    @2
    @10
    @4
    cP
    cR
    vk
    cO
    cQ
    gsumply1eq.p
    @17
    @2
    eqid
    @4
    eqid
    ply1coe1eq
    bicomd
    syl3anc
    wph
    @6
    @8
    vk
    cn0
    wph
    @1
    cn0
    wcel
    #
    wa
    #
    @3
    cA
    @5
    cB
    @22
    @3
    @1
    cP
    vl
    cn0
    vk
    vl
    cv
    #
    cA
    csb
    #
    @23
    cX
    c.ex
    co
    #
    c.as
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cA
    @22
    @1
    @2
    @29
    @22
    cO
    @28
    cco1
    @22
    cO
    @16
    @28
    wph
    cO
    @16
    wceq
    @21
    gsumply1eq.o
    adantr
    @15
    @27
    cP
    cgsu
    vk
    vl
    cn0
    @14
    @26
    vl
    @14
    nfcv
    vk
    @24
    @25
    c.as
    vk
    @23
    cA
    nfcsb1v
    #
    vk
    c.as
    nfcv
    #
    vk
    @25
    nfcv
    #
    nfov
    @1
    @23
    wceq
    #
    cA
    @24
    @13
    @25
    c.as
    vk
    @23
    cA
    csbeq1a
    #
    @1
    @23
    cX
    c.ex
    oveq1
    #
    oveq12d
    cbvmpt
    oveq2i
    syl6eq
    fveq2d
    fveq1d
    @22
    @30
    vl
    @1
    @24
    csb
    #
    cA
    @22
    @24
    @10
    cP
    cR
    vl
    c.ex
    c.as
    cK
    @1
    cX
    c.0
    gsumply1eq.p
    @17
    gsumply1eq.x
    gsumply1eq.e
    wph
    @9
    @21
    gsumply1eq.r
    adantr
    #
    gsumply1eq.k
    gsumply1eq.m
    gsumply1eq.0
    wph
    @24
    cK
    wcel
    #
    vl
    cn0
    wral
    #
    @21
    wph
    cA
    cK
    wcel
    #
    vk
    cn0
    wral
    @40
    gsumply1eq.a
    @41
    @39
    vk
    vl
    cn0
    @41
    vl
    nfv
    vk
    @24
    cK
    @31
    nfel1
    @34
    cA
    @24
    cK
    @35
    eleq1d
    cbvral
    sylib
    adantr
    wph
    vl
    cn0
    @24
    cmpt
    #
    c.0
    cfsupp
    wbr
    @21
    wph
    @42
    vk
    cn0
    cA
    cmpt
    c.0
    cfsupp
    vk
    vl
    cn0
    cA
    @24
    vl
    cA
    nfcv
    @31
    @35
    cbvmpt
    gsumply1eq.f1
    syl5eqbrr
    adantr
    wph
    @21
    simpr
    #
    gsummoncoe1
    @37
    vk
    @1
    cA
    csb
    cA
    vk
    vl
    @1
    cA
    csbco
    vk
    cA
    csbid
    eqtri
    syl6eq
    eqtrd
    @22
    @5
    @1
    cP
    vl
    cn0
    vk
    @23
    cB
    csb
    #
    @25
    c.as
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cB
    @22
    @1
    @4
    @48
    @22
    cQ
    @47
    cco1
    @22
    cQ
    @20
    @47
    wph
    cQ
    @20
    wceq
    @21
    gsumply1eq.q
    adantr
    @22
    @19
    @46
    cP
    cgsu
    @19
    @46
    wceq
    @22
    vk
    vl
    cn0
    @18
    @45
    vl
    @18
    nfcv
    vk
    @44
    @25
    c.as
    vk
    @23
    cB
    nfcsb1v
    #
    @32
    @33
    nfov
    @34
    cB
    @44
    @13
    @25
    c.as
    vk
    @23
    cB
    csbeq1a
    #
    @36
    oveq12d
    cbvmpt
    a1i
    oveq2d
    eqtrd
    fveq2d
    fveq1d
    @22
    @49
    vl
    @1
    @44
    csb
    #
    cB
    @22
    @44
    @10
    cP
    cR
    vl
    c.ex
    c.as
    cK
    @1
    cX
    c.0
    gsumply1eq.p
    @17
    gsumply1eq.x
    gsumply1eq.e
    @38
    gsumply1eq.k
    gsumply1eq.m
    gsumply1eq.0
    wph
    @44
    cK
    wcel
    #
    vl
    cn0
    wral
    #
    @21
    wph
    cB
    cK
    wcel
    #
    vk
    cn0
    wral
    @54
    gsumply1eq.b
    @55
    @53
    vk
    vl
    cn0
    @55
    vl
    nfv
    vk
    @44
    cK
    @50
    nfel1
    @34
    cB
    @44
    cK
    @51
    eleq1d
    cbvral
    sylib
    adantr
    wph
    vl
    cn0
    @44
    cmpt
    #
    c.0
    cfsupp
    wbr
    @21
    wph
    @56
    vk
    cn0
    cB
    cmpt
    c.0
    cfsupp
    vk
    vl
    cn0
    cB
    @44
    vl
    cB
    nfcv
    @50
    @51
    cbvmpt
    gsumply1eq.f2
    syl5eqbrr
    adantr
    @43
    gsummoncoe1
    @52
    vk
    @1
    cB
    csb
    cB
    vk
    vl
    @1
    cB
    csbco
    vk
    cB
    csbid
    eqtri
    syl6eq
    eqtrd
    eqeq12d
    ralbidva
    bitrd
end
