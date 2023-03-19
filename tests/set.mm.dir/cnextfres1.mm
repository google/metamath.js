include "ccnext.mm"
include "co.mm"
include "cfv.mm"
include "cres.mm"
include "wfn.mm"
include "wss.mm"
include "wf.mm"
include "cnextf.mm"
include "ffn.mm"
include "syl.mm"
include "fnssres.mm"
include "syl2anc.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cnei.mm"
include "crest.mm"
include "cflf.mm"
include "cuni.mm"
include "wceq.mm"
include "fvres.mm"
include "adantl.mm"
include "sselda.mm"
include "cnextfvval.mm"
include "syldan.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "cima.mm"
include "wrex.mm"
include "wral.mm"
include "ffvelrnda.mm"
include "simpr.mm"
include "ctop.mm"
include "restuni.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "ccn.mm"
include "wb.mm"
include "cvv.mm"
include "ccl.mm"
include "fvex.mm"
include "syl6eqelr.mm"
include "ssexd.mm"
include "resttop.mm"
include "cha.mm"
include "haustop.mm"
include "feq2d.mm"
include "mpbid.mm"
include "eqid.mm"
include "cnnei.mm"
include "syl3anc.mm"
include "r19.21bi.mm"
include "snssi.mm"
include "neitr.mm"
include "rexeqdv.mm"
include "ralrimiva.mm"
include "ctopon.mm"
include "cfil.mm"
include "toptopon.mm"
include "biimpi.mm"
include "3syl.mm"
include "eleqtrrd.mm"
include "sylib.mm"
include "trnei.mm"
include "flfnei.mm"
include "mpbir2and.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "sneq.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "fveq1d.mm"
include "neeq1d.mm"
include "imbi12d.mm"
include "chvarv.mm"
include "hausflf2.mm"
include "syl31anc.mm"
include "en1eqsn.mm"
include "unieqd.mm"
include "unisn.mm"
include "syl6eq.mm"
include "3eqtrd.mm"
include "eqfnfvd.mm"

theorem cnextfres1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cJ: class J
  let cK: class K
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let cX: class X
  let vb: setvar b
  let vd: setvar d
  let vu: setvar u
  let vz: setvar z
  let vc: setvar c
  assume cnextf.1: |- C = U. J
  assume cnextf.2: |- B = U. K
  assume cnextf.3: |- ( ph -> J e. Top )
  assume cnextf.4: |- ( ph -> K e. Haus )
  assume cnextf.5: |- ( ph -> F : A --> B )
  assume cnextf.a: |- ( ph -> A C_ C )
  assume cnextf.6: |- ( ph -> ( ( cls ` J ) ` A ) = C )
  assume cnextf.7: |- ( ( ph /\ x e. C ) -> ( ( K fLimf ( ( ( nei ` J ) ` { x } ) |`t A ) ) ` F ) =/= (/) )
  assume cnextcn.8: |- ( ph -> K e. Reg )
  assume cnextfres1.1: |- ( ph -> F e. ( ( J |`t A ) Cn K ) )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint F x
  disjoint J x
  disjoint K x
  disjoint ph x
  disjoint v w
  disjoint v y
  disjoint A v
  disjoint w y
  disjoint A w
  disjoint A y
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint F y
  disjoint J y
  disjoint K y
  disjoint X x
  disjoint X y
  disjoint ph y
  disjoint b d
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint d u
  disjoint d v
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint A d
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint b w
  disjoint B b
  disjoint u w
  disjoint B u
  disjoint v w
  disjoint B v
  disjoint w x
  disjoint w y
  disjoint B w
  disjoint b c
  disjoint C b
  disjoint c d
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint C c
  disjoint d w
  disjoint C d
  disjoint C u
  disjoint C v
  disjoint C w
  disjoint C y
  disjoint F b
  disjoint c z
  disjoint F c
  disjoint F d
  disjoint F u
  disjoint F v
  disjoint w z
  disjoint F w
  disjoint F z
  disjoint J b
  disjoint J c
  disjoint J d
  disjoint J u
  disjoint J v
  disjoint J w
  disjoint J z
  disjoint K b
  disjoint K c
  disjoint K d
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint K z
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph z
  assert |- ( ph -> ( ( ( J CnExt K ) ` F ) |` A ) = F )

  proof
    wph
    vy
    cA
    cF
    cJ
    cK
    ccnext
    co
    cfv
    #
    cA
    cres
    #
    cF
    wph
    @0
    cC
    wfn
    #
    cA
    cC
    wss
    #
    @1
    cA
    wfn
    wph
    cC
    cB
    @0
    wf
    @2
    wph
    vx
    cA
    cB
    cC
    cF
    cJ
    cK
    cnextf.1
    cnextf.2
    cnextf.3
    cnextf.4
    cnextf.5
    cnextf.a
    cnextf.6
    cnextf.7
    cnextf
    cC
    cB
    @0
    ffn
    syl
    cnextf.a
    cC
    cA
    @0
    fnssres
    syl2anc
    wph
    cA
    cB
    cF
    wf
    #
    cF
    cA
    wfn
    cnextf.5
    cA
    cB
    cF
    ffn
    syl
    wph
    vy
    cv
    #
    cA
    wcel
    #
    wa
    #
    @5
    @1
    cfv
    #
    @5
    @0
    cfv
    #
    cF
    cK
    @5
    csn
    #
    cJ
    cnei
    cfv
    #
    cfv
    #
    cA
    crest
    co
    #
    cflf
    co
    #
    cfv
    #
    cuni
    #
    @5
    cF
    cfv
    #
    @6
    @8
    @9
    wceq
    wph
    @5
    cA
    @0
    fvres
    adantl
    wph
    @6
    @5
    cC
    wcel
    #
    @9
    @16
    wceq
    wph
    cA
    cC
    @5
    cnextf.a
    sselda
    #
    wph
    vx
    cA
    cB
    cC
    cF
    cJ
    cK
    @5
    cnextf.1
    cnextf.2
    cnextf.3
    cnextf.4
    cnextf.5
    cnextf.a
    cnextf.6
    cnextf.7
    cnextfvval
    syldan
    @7
    @16
    @17
    csn
    #
    cuni
    @17
    @7
    @15
    @20
    @7
    @17
    @15
    wcel
    #
    @15
    c1o
    cen
    wbr
    #
    @15
    @20
    wceq
    @7
    @21
    @17
    cB
    wcel
    #
    cF
    vv
    cv
    cima
    vw
    cv
    #
    wss
    #
    vv
    @13
    wrex
    #
    vw
    @20
    cK
    cnei
    cfv
    cfv
    #
    wral
    #
    wph
    cA
    cB
    @5
    cF
    cnextf.5
    ffvelrnda
    @7
    @26
    vw
    @27
    @7
    @24
    @27
    wcel
    #
    wa
    @25
    vv
    @10
    cJ
    cA
    crest
    co
    #
    cnei
    cfv
    cfv
    #
    wrex
    #
    @26
    @7
    @32
    vw
    @27
    wph
    @6
    @5
    @30
    cuni
    #
    wcel
    @32
    vw
    @27
    wral
    #
    @7
    @5
    cA
    @33
    wph
    @6
    simpr
    wph
    cA
    @33
    wceq
    #
    @6
    wph
    cJ
    ctop
    wcel
    #
    @3
    @35
    cnextf.3
    cnextf.a
    cA
    cJ
    cC
    cnextf.1
    restuni
    syl2anc
    #
    adantr
    eleqtrd
    wph
    @34
    vy
    @33
    wph
    cF
    @30
    cK
    ccn
    co
    wcel
    #
    @34
    vy
    @33
    wral
    #
    cnextfres1.1
    wph
    @30
    ctop
    wcel
    #
    cK
    ctop
    wcel
    #
    @33
    cB
    cF
    wf
    #
    @38
    @39
    wb
    wph
    @36
    cA
    cvv
    wcel
    @40
    cnextf.3
    wph
    cA
    cC
    cvv
    wph
    cC
    cA
    cJ
    ccl
    cfv
    #
    cfv
    #
    cvv
    cnextf.6
    cA
    @43
    fvex
    syl6eqelr
    cnextf.a
    ssexd
    cA
    cJ
    cvv
    resttop
    syl2anc
    wph
    cK
    cha
    wcel
    #
    @41
    cnextf.4
    cK
    haustop
    #
    syl
    wph
    @4
    @42
    cnextf.5
    wph
    cA
    @33
    cB
    cF
    @37
    feq2d
    mpbid
    vw
    vv
    cF
    @30
    cK
    @33
    cB
    vy
    @33
    eqid
    cnextf.2
    cnnei
    syl3anc
    mpbid
    r19.21bi
    syldan
    r19.21bi
    @7
    @32
    @26
    wb
    @29
    @7
    @25
    vv
    @31
    @13
    @7
    @36
    @3
    @10
    cA
    wss
    #
    @31
    @13
    wceq
    wph
    @36
    @6
    cnextf.3
    adantr
    wph
    @3
    @6
    cnextf.a
    adantr
    #
    @6
    @47
    wph
    @5
    cA
    snssi
    adantl
    cA
    @10
    cJ
    cC
    cnextf.1
    neitr
    syl3anc
    rexeqdv
    adantr
    mpbid
    ralrimiva
    @7
    cK
    cB
    ctopon
    cfv
    wcel
    #
    @13
    cA
    cfil
    cfv
    wcel
    #
    @4
    @21
    @23
    @28
    wa
    wb
    @7
    @45
    @41
    @49
    wph
    @45
    @6
    cnextf.4
    adantr
    #
    @46
    @41
    @49
    cK
    cB
    cnextf.2
    toptopon
    biimpi
    3syl
    @7
    @5
    @44
    wcel
    #
    @50
    @7
    @5
    cC
    @44
    @19
    wph
    @44
    cC
    wceq
    @6
    cnextf.6
    adantr
    eleqtrrd
    @7
    cJ
    cC
    ctopon
    cfv
    wcel
    #
    @3
    @18
    @52
    @50
    wb
    wph
    @53
    @6
    wph
    @36
    @53
    cnextf.3
    cJ
    cC
    cnextf.1
    toptopon
    sylib
    adantr
    @48
    @19
    cA
    @5
    cJ
    cC
    trnei
    syl3anc
    mpbid
    #
    wph
    @4
    @6
    cnextf.5
    adantr
    #
    @17
    vw
    cF
    cK
    @13
    cB
    cA
    vv
    flfnei
    syl3anc
    mpbir2and
    @7
    @45
    @50
    @4
    @15
    c0
    wne
    #
    @22
    @51
    @54
    @55
    wph
    @6
    @18
    @56
    @19
    wph
    vx
    cv
    #
    cC
    wcel
    #
    wa
    #
    cF
    cK
    @57
    csn
    #
    @11
    cfv
    #
    cA
    crest
    co
    #
    cflf
    co
    #
    cfv
    #
    c0
    wne
    #
    wi
    wph
    @18
    wa
    #
    @56
    wi
    vx
    vy
    @57
    @5
    wceq
    #
    @59
    @66
    @65
    @56
    @67
    @58
    @18
    wph
    @57
    @5
    cC
    eleq1
    anbi2d
    @67
    @64
    @15
    c0
    @67
    cF
    @63
    @14
    @67
    @62
    @13
    cK
    cflf
    @67
    @61
    @12
    cA
    crest
    @67
    @60
    @10
    @11
    @57
    @5
    sneq
    fveq2d
    oveq1d
    oveq2d
    fveq1d
    neeq1d
    imbi12d
    cnextf.7
    chvarv
    syldan
    cF
    cK
    @13
    cB
    cA
    cnextf.2
    hausflf2
    syl31anc
    @17
    @15
    en1eqsn
    syl2anc
    unieqd
    @17
    @5
    cF
    fvex
    unisn
    syl6eq
    3eqtrd
    eqfnfvd
end
