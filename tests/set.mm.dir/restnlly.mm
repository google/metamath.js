include "cnlly.mm"
include "clly.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "ctop.mm"
include "wel.mm"
include "crest.mm"
include "co.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "nllytop.mm"
include "adantl.mm"
include "w3a.mm"
include "wss.mm"
include "nlly2i.mm"
include "3adant1l.mm"
include "simprl.mm"
include "simprr2.mm"
include "simplr.mm"
include "elpwid.mm"
include "sstrd.mm"
include "selpw.mm"
include "sylibr.mm"
include "elind.mm"
include "simprr1.mm"
include "wceq.mm"
include "simpll1.mm"
include "simprd.mm"
include "syl.mm"
include "restabs.mm"
include "syl3anc.mm"
include "wi.mm"
include "simprr3.mm"
include "simpld.mm"
include "expr.mm"
include "ralrimiva.mm"
include "df-ss.mm"
include "sylib.mm"
include "elrestr.mm"
include "eqeltrrd.mm"
include "eleq2.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "jca32.mm"
include "ex.mm"
include "reximdv2.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "islly.mm"
include "sylanbrc.mm"
include "ssrdv.mm"
include "llyssnlly.mm"
include "a1i.mm"
include "eqssd.mm"

theorem restnlly
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vj: setvar j
  let vk: setvar k
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vy: setvar y
  let vz: setvar z
  let cJ: class J
  let cX: class X
  assume restlly.1: |- ( ( ph /\ ( j e. A /\ x e. j ) ) -> ( j |`t x ) e. A )

  disjoint j x
  disjoint A j
  disjoint A x
  disjoint j ph
  disjoint ph x
  disjoint j k
  disjoint j s
  disjoint j u
  disjoint j v
  disjoint j y
  disjoint j z
  disjoint k s
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint J j
  disjoint J u
  disjoint J v
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint k ph
  disjoint ph s
  disjoint ph u
  disjoint ph y
  disjoint ph z
  disjoint X u
  disjoint X y
  disjoint X z
  assert |- ( ph -> N-Locally A = Locally A )

  proof
    wph
    cA
    cnlly
    #
    cA
    clly
    #
    wph
    vk
    @0
    @1
    wph
    vk
    cv
    #
    @0
    wcel
    #
    @2
    @1
    wcel
    #
    wph
    @3
    wa
    #
    @2
    ctop
    wcel
    #
    vu
    vx
    wel
    #
    @2
    vx
    cv
    #
    crest
    co
    #
    cA
    wcel
    #
    wa
    #
    vx
    @2
    vy
    cv
    #
    cpw
    #
    cin
    #
    wrex
    #
    vu
    @12
    wral
    vy
    @2
    wral
    @4
    @3
    @6
    wph
    cA
    @2
    nllytop
    #
    adantl
    @5
    @15
    vy
    vu
    @2
    @12
    @5
    vy
    vk
    wel
    #
    vu
    vy
    wel
    #
    @15
    @5
    @17
    @18
    w3a
    #
    @7
    @8
    vs
    cv
    #
    wss
    #
    @2
    @20
    crest
    co
    #
    cA
    wcel
    #
    w3a
    #
    vx
    @2
    wrex
    #
    vs
    @13
    wrex
    #
    @15
    @3
    @17
    @18
    @26
    wph
    vx
    cA
    vu
    cv
    @12
    @2
    vs
    nlly2i
    3adant1l
    @19
    @25
    @15
    vs
    @13
    @19
    @20
    @13
    wcel
    #
    wa
    #
    @24
    @11
    vx
    @2
    @14
    @28
    vx
    vk
    wel
    #
    @24
    wa
    #
    @8
    @14
    wcel
    #
    @11
    wa
    @28
    @30
    wa
    #
    @31
    @7
    @10
    @32
    @2
    @13
    @8
    @28
    @29
    @24
    simprl
    #
    @32
    @8
    @12
    wss
    @8
    @13
    wcel
    @32
    @8
    @20
    @12
    @7
    @21
    @23
    @29
    @28
    simprr2
    #
    @32
    @20
    @12
    @19
    @27
    @30
    simplr
    #
    elpwid
    sstrd
    vx
    @12
    selpw
    sylibr
    elind
    @7
    @21
    @23
    @29
    @28
    simprr1
    @32
    @22
    @8
    crest
    co
    #
    @9
    cA
    @32
    @6
    @21
    @27
    @36
    @9
    wceq
    @32
    @3
    @6
    @32
    wph
    @3
    @5
    @17
    @18
    @27
    @30
    simpll1
    #
    simprd
    @16
    syl
    #
    @34
    @35
    @8
    @20
    @2
    ctop
    @13
    restabs
    syl3anc
    @32
    @23
    vx
    vj
    wel
    #
    vj
    cv
    #
    @8
    crest
    co
    #
    cA
    wcel
    #
    wi
    #
    vj
    cA
    wral
    #
    @8
    @22
    wcel
    #
    @36
    cA
    wcel
    #
    @7
    @21
    @23
    @29
    @28
    simprr3
    @32
    wph
    @44
    @32
    wph
    @3
    @37
    simpld
    wph
    @43
    vj
    cA
    wph
    @40
    cA
    wcel
    @39
    @42
    restlly.1
    expr
    ralrimiva
    syl
    @32
    @8
    @20
    cin
    #
    @8
    @22
    @32
    @21
    @47
    @8
    wceq
    @34
    @8
    @20
    df-ss
    sylib
    @32
    @6
    @27
    @29
    @47
    @22
    wcel
    @38
    @35
    @33
    @8
    @20
    @2
    ctop
    @13
    elrestr
    syl3anc
    eqeltrrd
    @43
    @45
    @46
    wi
    vj
    @22
    cA
    @40
    @22
    wceq
    #
    @39
    @45
    @42
    @46
    @40
    @22
    @8
    eleq2
    @48
    @41
    @36
    cA
    @40
    @22
    @8
    crest
    oveq1
    eleq1d
    imbi12d
    rspcv
    syl3c
    eqeltrrd
    jca32
    ex
    reximdv2
    rexlimdva
    mpd
    3expb
    ralrimivva
    vy
    vu
    vx
    cA
    @2
    islly
    sylanbrc
    ex
    ssrdv
    @1
    @0
    wss
    wph
    cA
    llyssnlly
    a1i
    eqssd
end
