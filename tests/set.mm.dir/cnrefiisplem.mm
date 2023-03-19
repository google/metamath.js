include "crp.mm"
include "wcel.mm"
include "cv.mm"
include "cc.mm"
include "wne.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "cim.mm"
include "wceq.mm"
include "simpr.mm"
include "absimnre.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "adantlr.mm"
include "cin.mm"
include "csn.mm"
include "cdif.mm"
include "simpll.mm"
include "ciun.mm"
include "cun.mm"
include "wn.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "nelsn.mm"
include "elunnel1.mm"
include "syl2an.mm"
include "eliun.mm"
include "sylib.mm"
include "velsn.mm"
include "rexbii.mm"
include "adantll.mm"
include "eldifi.mm"
include "elin2d.mm"
include "ad2antlr.mm"
include "ad2antrr.mm"
include "subcld.mm"
include "eldifsni.mm"
include "subne0d.mm"
include "absrpcld.mm"
include "rexlimdva2.mm"
include "sylc.mm"
include "pm2.61dane.mm"
include "ssd.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "wor.mm"
include "cfn.mm"
include "c0.mm"
include "wss.mm"
include "xrltso.mm"
include "a1i.mm"
include "snfi.mm"
include "inss1.mm"
include "ssdifssd.mm"
include "ssfid.mm"
include "rgenw.mm"
include "iunfi.mm"
include "sylancl.mm"
include "unfid.mm"
include "syl5eqel.mm"
include "fvex.mm"
include "snid.mm"
include "elun1.mm"
include "ax-mp.mm"
include "eleqtrri.mm"
include "ne0d.mm"
include "rpssxr.mm"
include "syl6ss.mm"
include "fiinfcl.mm"
include "syl13anc.mm"
include "sseldd.mm"
include "cr.mm"
include "rpred.mm"
include "imcld.mm"
include "recnd.mm"
include "abscld.mm"
include "recn.mm"
include "adantl.mm"
include "infxrlb.mm"
include "absimlere.mm"
include "letrd.mm"
include "syl5eqbr.mm"
include "ad4ant14.mm"
include "sylanb.mm"
include "ad4ant24.mm"
include "elind.mm"
include "eldifd.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "sneqd.mm"
include "eliuni.mm"
include "cbviunv.mm"
include "syl6eleq.mm"
include "elun2.mm"
include "syl.mm"
include "syl6eleqr.mm"
include "syl2anc.mm"
include "adantllr.mm"
include "syldan.mm"
include "pm2.61dan.mm"
include "ex.mm"
include "ralrimiva.mm"
include "breq1.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "rspcev.mm"

theorem cnrefiisplem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cX: class X
  let vw: setvar w
  let vk: setvar k
  assume cnrefiisplem.a: |- ( ph -> A e. CC )
  assume cnrefiisplem.n: |- ( ph -> -. A e. RR )
  assume cnrefiisplem.b: |- ( ph -> B e. Fin )
  assume cnrefiisplem.c: |- C = ( RR u. B )
  assume cnrefiisplem.d: |- D = ( { ( abs ` ( Im ` A ) ) } u. U_ y e. ( ( B i^i CC ) \ { A } ) { ( abs ` ( y - A ) ) } )
  assume cnrefiisplem.x: |- X = inf ( D , RR* , < )

  disjoint A y
  disjoint A x
  disjoint x y
  disjoint B y
  disjoint C x
  disjoint X x
  disjoint X y
  disjoint ph y
  disjoint A w
  disjoint w y
  disjoint B w
  disjoint D w
  disjoint ph w
  disjoint k x
  assert |- ( ph -> E. x e. RR+ A. y e. C ( ( y e. CC /\ y =/= A ) -> x <_ ( abs ` ( y - A ) ) ) )

  proof
    wph
    cX
    crp
    wcel
    vy
    cv
    #
    cc
    wcel
    #
    @0
    cA
    wne
    #
    wa
    #
    cX
    @0
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    wi
    #
    vy
    cC
    wral
    #
    @3
    vx
    cv
    #
    @5
    cle
    wbr
    #
    wi
    #
    vy
    cC
    wral
    #
    vx
    crp
    wrex
    wph
    cD
    crp
    cX
    wph
    vw
    cD
    crp
    wph
    vw
    cv
    #
    cD
    wcel
    #
    wa
    #
    @13
    crp
    wcel
    #
    @13
    cA
    cim
    cfv
    #
    cabs
    cfv
    #
    wph
    @13
    @18
    wceq
    #
    @16
    @14
    wph
    @19
    wa
    @13
    @18
    crp
    wph
    @19
    simpr
    wph
    @18
    crp
    wcel
    @19
    wph
    cA
    cnrefiisplem.a
    cnrefiisplem.n
    absimnre
    adantr
    eqeltrd
    adantlr
    @15
    @13
    @18
    wne
    #
    wa
    wph
    @13
    @5
    wceq
    #
    vy
    cB
    cc
    cin
    #
    cA
    csn
    #
    cdif
    #
    wrex
    #
    @16
    wph
    @14
    @20
    simpll
    @14
    @20
    @25
    wph
    @14
    @20
    wa
    #
    @13
    @5
    csn
    #
    wcel
    #
    vy
    @24
    wrex
    #
    @25
    @26
    @13
    vy
    @24
    @27
    ciun
    #
    wcel
    #
    @29
    @14
    @13
    @18
    csn
    #
    @30
    cun
    #
    wcel
    #
    @13
    @32
    wcel
    wn
    @31
    @20
    @14
    @34
    cD
    @33
    @13
    cnrefiisplem.d
    eleq2i
    biimpi
    @13
    @18
    nelsn
    @13
    @32
    @30
    elunnel1
    syl2an
    vy
    @13
    @24
    @27
    eliun
    sylib
    @28
    @21
    vy
    @24
    vw
    @5
    velsn
    rexbii
    sylib
    adantll
    wph
    @21
    @16
    vy
    @24
    wph
    @0
    @24
    wcel
    #
    wa
    #
    @21
    wa
    #
    @13
    @5
    crp
    @36
    @21
    simpr
    @37
    @4
    @37
    @0
    cA
    @35
    @1
    wph
    @21
    @35
    cB
    cc
    @0
    @0
    @22
    @23
    eldifi
    elin2d
    ad2antlr
    #
    wph
    cA
    cc
    wcel
    #
    @35
    @21
    cnrefiisplem.a
    ad2antrr
    #
    subcld
    @37
    @0
    cA
    @38
    @40
    @35
    @2
    wph
    @21
    @0
    @22
    cA
    eldifsni
    ad2antlr
    subne0d
    absrpcld
    eqeltrd
    rexlimdva2
    sylc
    pm2.61dane
    ssd
    #
    wph
    cX
    cD
    cxr
    clt
    cinf
    #
    cD
    cnrefiisplem.x
    wph
    cxr
    clt
    wor
    #
    cD
    cfn
    wcel
    cD
    c0
    wne
    cD
    cxr
    wss
    #
    @42
    cD
    wcel
    @43
    wph
    xrltso
    a1i
    wph
    cD
    @33
    cfn
    cnrefiisplem.d
    wph
    @32
    @30
    @32
    cfn
    wcel
    wph
    @18
    snfi
    a1i
    wph
    @24
    cfn
    wcel
    @27
    cfn
    wcel
    #
    vy
    @24
    wral
    @30
    cfn
    wcel
    wph
    cB
    @24
    cnrefiisplem.b
    wph
    @22
    cB
    @23
    @22
    cB
    wss
    wph
    cB
    cc
    inss1
    a1i
    ssdifssd
    ssfid
    @45
    vy
    @24
    @5
    snfi
    rgenw
    vy
    @24
    @27
    iunfi
    sylancl
    unfid
    syl5eqel
    wph
    cD
    @18
    @18
    cD
    wcel
    #
    wph
    @18
    @33
    cD
    @18
    @32
    wcel
    @18
    @33
    wcel
    @18
    @17
    cabs
    fvex
    snid
    @18
    @32
    @30
    elun1
    ax-mp
    cnrefiisplem.d
    eleqtrri
    #
    a1i
    ne0d
    wph
    cD
    crp
    cxr
    @41
    rpssxr
    syl6ss
    #
    cxr
    cD
    clt
    fiinfcl
    syl13anc
    #
    syl5eqel
    sseldd
    wph
    @7
    vy
    cC
    wph
    @0
    cC
    wcel
    #
    wa
    #
    @3
    @6
    @51
    @3
    wa
    #
    @0
    cr
    wcel
    #
    @6
    wph
    @53
    @6
    @50
    @3
    wph
    @53
    wa
    #
    cX
    @42
    @5
    cle
    cnrefiisplem.x
    @54
    @42
    @18
    @5
    wph
    @42
    cr
    wcel
    @53
    wph
    @42
    wph
    cD
    crp
    @42
    @41
    @49
    sseldd
    rpred
    adantr
    @54
    @17
    wph
    @17
    cc
    wcel
    @53
    wph
    @17
    wph
    cA
    cnrefiisplem.a
    imcld
    recnd
    adantr
    abscld
    @54
    @4
    @54
    @0
    cA
    @53
    @1
    wph
    @0
    recn
    adantl
    wph
    @39
    @53
    cnrefiisplem.a
    adantr
    #
    subcld
    abscld
    @54
    @44
    @46
    @42
    @18
    cle
    wbr
    wph
    @44
    @53
    @48
    adantr
    @47
    cD
    @18
    infxrlb
    sylancl
    @54
    cA
    @0
    @55
    wph
    @53
    simpr
    absimlere
    letrd
    syl5eqbr
    ad4ant14
    @52
    @53
    wn
    #
    @0
    cB
    wcel
    #
    @6
    @50
    @56
    @57
    wph
    @3
    @50
    @0
    cr
    cB
    cun
    #
    wcel
    @56
    @57
    cC
    @58
    @0
    cnrefiisplem.c
    eleq2i
    @0
    cr
    cB
    elunnel1
    sylanb
    ad4ant24
    wph
    @3
    @57
    @6
    @50
    wph
    @3
    wa
    @57
    wa
    #
    cX
    @42
    @5
    cle
    cnrefiisplem.x
    @59
    @44
    @5
    cD
    wcel
    #
    @42
    @5
    cle
    wbr
    wph
    @44
    @3
    @57
    @48
    ad2antrr
    @3
    @57
    @60
    wph
    @3
    @57
    wa
    #
    @5
    @33
    cD
    @61
    @5
    @30
    wcel
    @5
    @33
    wcel
    @61
    @5
    vw
    @24
    @13
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    csn
    #
    ciun
    #
    @30
    @61
    @35
    @5
    @27
    wcel
    @5
    @65
    wcel
    @61
    @0
    @22
    @23
    @61
    cB
    cc
    @0
    @3
    @57
    simpr
    @1
    @2
    @57
    simpll
    elind
    @2
    @0
    @23
    wcel
    wn
    @1
    @57
    @0
    cA
    nelsn
    ad2antlr
    eldifd
    @5
    @4
    cabs
    fvex
    snid
    vw
    @0
    @64
    @27
    @24
    @5
    @13
    @0
    wceq
    #
    @63
    @5
    @66
    @62
    @4
    cabs
    @13
    @0
    cA
    cmin
    oveq1
    fveq2d
    sneqd
    #
    eliuni
    sylancl
    vw
    vy
    @24
    @64
    @27
    @67
    cbviunv
    syl6eleq
    @5
    @30
    @32
    elun2
    syl
    cnrefiisplem.d
    syl6eleqr
    adantll
    cD
    @5
    infxrlb
    syl2anc
    syl5eqbr
    adantllr
    syldan
    pm2.61dan
    ex
    ralrimiva
    @12
    @8
    vx
    cX
    crp
    @9
    cX
    wceq
    #
    @11
    @7
    vy
    cC
    @68
    @10
    @6
    @3
    @9
    cX
    @5
    cle
    breq1
    imbi2d
    ralbidv
    rspcev
    syl2anc
end
