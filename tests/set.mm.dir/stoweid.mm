include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "c1.mm"
include "c4.mm"
include "cdiv.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "clt.mm"
include "wral.mm"
include "wrex.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "cmpt.mm"
include "wcel.mm"
include "cr.mm"
include "ralrimiva.mm"
include "1re.mm"
include "id.mm"
include "mpteq2dv.mm"
include "eleq1d.mm"
include "rspccv.mm"
include "mpisyl.mm"
include "adantr.mm"
include "stoweidlem9.mm"
include "wn.mm"
include "crn.mm"
include "cinf.mm"
include "nfv.mm"
include "nfan.mm"
include "eqid.mm"
include "ccmp.mm"
include "wss.mm"
include "caddc.mm"
include "3adant1r.mm"
include "cmul.mm"
include "adantlr.mm"
include "wne.mm"
include "w3a.mm"
include "crp.mm"
include "4re.mm"
include "4pos.mm"
include "elrpii.mm"
include "a1i.mm"
include "rpreccld.mm"
include "ifcld.mm"
include "neqne.mm"
include "adantl.mm"
include "c3.mm"
include "rpred.mm"
include "4ne0.mm"
include "rereccli.mm"
include "3re.mm"
include "3ne0.mm"
include "cxr.mm"
include "rpxrd.mm"
include "xrmin2.mm"
include "syl2anc.mm"
include "3lt4.mm"
include "3pos.mm"
include "ltrecii.mm"
include "mpbi.mm"
include "lelttrd.mm"
include "stoweidlem62.mm"
include "pm2.61dan.mm"
include "xrmin1.mm"
include "ad2antrr.mm"
include "wi.mm"
include "wf.mm"
include "cc.mm"
include "simplr.mm"
include "sseldd.mm"
include "fcnre.mm"
include "jca.mm"
include "ffvelrn.mm"
include "recn.mm"
include "3syl.mm"
include "subcld.mm"
include "abscld.mm"
include "cc0.mm"
include "3pm3.2i.mm"
include "redivcl.mm"
include "mp1i.mm"
include "ltletr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "ralimdaa.mm"
include "reximdva.mm"
include "mpd.mm"

theorem stoweid
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cA: class A
  let cC: class C
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cE: class E
  let cF: class F
  let cJ: class J
  let cK: class K
  let vr: setvar r
  let vk: setvar k
  assume stoweid.1: |- F/_ t F
  assume stoweid.2: |- F/ t ph
  assume stoweid.3: |- K = ( topGen ` ran (,) )
  assume stoweid.4: |- ( ph -> J e. Comp )
  assume stoweid.5: |- T = U. J
  assume stoweid.6: |- C = ( J Cn K )
  assume stoweid.7: |- ( ph -> A C_ C )
  assume stoweid.8: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) + ( g ` t ) ) ) e. A )
  assume stoweid.9: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. A )
  assume stoweid.10: |- ( ( ph /\ x e. RR ) -> ( t e. T |-> x ) e. A )
  assume stoweid.11: |- ( ( ph /\ ( r e. T /\ t e. T /\ r =/= t ) ) -> E. h e. A ( h ` r ) =/= ( h ` t ) )
  assume stoweid.12: |- ( ph -> F e. C )
  assume stoweid.13: |- ( ph -> E e. RR+ )

  disjoint f g
  disjoint f t
  disjoint A f
  disjoint g t
  disjoint A g
  disjoint A t
  disjoint f h
  disjoint f r
  disjoint f x
  disjoint h r
  disjoint h t
  disjoint h x
  disjoint A h
  disjoint r t
  disjoint r x
  disjoint A r
  disjoint t x
  disjoint A x
  disjoint E f
  disjoint E g
  disjoint E t
  disjoint F f
  disjoint F g
  disjoint J f
  disjoint J r
  disjoint J t
  disjoint T f
  disjoint T g
  disjoint T t
  disjoint f ph
  disjoint g ph
  disjoint E h
  disjoint E r
  disjoint E x
  disjoint F h
  disjoint F r
  disjoint F x
  disjoint T h
  disjoint T r
  disjoint T x
  disjoint h ph
  disjoint ph r
  disjoint ph x
  disjoint K t
  disjoint k x
  assert |- ( ph -> E. f e. A A. t e. T ( abs ` ( ( f ` t ) - ( F ` t ) ) ) < E )

  proof
    wph
    vt
    cv
    #
    vf
    cv
    #
    cfv
    #
    @0
    cF
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cE
    c1
    c4
    cdiv
    co
    #
    cle
    wbr
    #
    cE
    @6
    cif
    #
    clt
    wbr
    #
    vt
    cT
    wral
    #
    vf
    cA
    wrex
    #
    @5
    cE
    clt
    wbr
    #
    vt
    cT
    wral
    #
    vf
    cA
    wrex
    wph
    cT
    c0
    wceq
    #
    @11
    wph
    @14
    wa
    vt
    cA
    cT
    vf
    @8
    cF
    wph
    @14
    simpr
    wph
    vt
    cT
    c1
    cmpt
    #
    cA
    wcel
    #
    @14
    wph
    vt
    cT
    vx
    cv
    #
    cmpt
    #
    cA
    wcel
    #
    vx
    cr
    wral
    c1
    cr
    wcel
    #
    @16
    wph
    @19
    vx
    cr
    stoweid.10
    ralrimiva
    1re
    @19
    @16
    vx
    c1
    cr
    @17
    c1
    wceq
    #
    @18
    @15
    cA
    @21
    vt
    cT
    @17
    c1
    @21
    id
    mpteq2dv
    eleq1d
    rspccv
    mpisyl
    adantr
    stoweidlem9
    wph
    @14
    wn
    #
    wa
    vx
    vt
    cA
    cC
    cT
    vf
    vg
    @8
    cF
    vt
    cT
    @3
    cF
    crn
    cr
    clt
    cinf
    cmin
    co
    cmpt
    #
    cJ
    cK
    vr
    vh
    stoweid.1
    wph
    @22
    vf
    wph
    vf
    nfv
    @22
    vf
    nfv
    nfan
    wph
    @22
    vt
    stoweid.2
    @22
    vt
    nfv
    nfan
    @23
    eqid
    stoweid.3
    stoweid.5
    wph
    cJ
    ccmp
    wcel
    @22
    stoweid.4
    adantr
    stoweid.6
    wph
    cA
    cC
    wss
    #
    @22
    stoweid.7
    adantr
    wph
    @1
    cA
    wcel
    #
    vg
    cv
    #
    cA
    wcel
    #
    vt
    cT
    @2
    @0
    @26
    cfv
    #
    caddc
    co
    cmpt
    cA
    wcel
    @22
    stoweid.8
    3adant1r
    wph
    @25
    @27
    vt
    cT
    @2
    @28
    cmul
    co
    cmpt
    cA
    wcel
    @22
    stoweid.9
    3adant1r
    wph
    @17
    cr
    wcel
    @19
    @22
    stoweid.10
    adantlr
    wph
    vr
    cv
    #
    cT
    wcel
    @0
    cT
    wcel
    #
    @29
    @0
    wne
    w3a
    @29
    vh
    cv
    #
    cfv
    @0
    @31
    cfv
    wne
    vh
    cA
    wrex
    @22
    stoweid.11
    adantlr
    wph
    cF
    cC
    wcel
    #
    @22
    stoweid.12
    adantr
    wph
    @8
    crp
    wcel
    @22
    wph
    @7
    cE
    @6
    crp
    stoweid.13
    wph
    c4
    c4
    crp
    wcel
    wph
    c4
    4re
    4pos
    elrpii
    a1i
    rpreccld
    #
    ifcld
    adantr
    @22
    cT
    c0
    wne
    wph
    cT
    c0
    neqne
    adantl
    wph
    @8
    c1
    c3
    cdiv
    co
    #
    clt
    wbr
    @22
    wph
    @8
    @6
    @34
    wph
    @7
    cE
    @6
    cr
    wph
    cE
    stoweid.13
    rpred
    #
    @6
    cr
    wcel
    #
    wph
    c4
    4re
    4ne0
    rereccli
    a1i
    #
    ifcld
    @37
    @34
    cr
    wcel
    wph
    c3
    3re
    3ne0
    rereccli
    a1i
    wph
    cE
    cxr
    wcel
    #
    @6
    cxr
    wcel
    #
    @8
    @6
    cle
    wbr
    wph
    cE
    stoweid.13
    rpxrd
    #
    wph
    @6
    @33
    rpxrd
    #
    cE
    @6
    xrmin2
    syl2anc
    @6
    @34
    clt
    wbr
    #
    wph
    c3
    c4
    clt
    wbr
    @42
    3lt4
    c3
    c4
    3re
    4re
    3pos
    4pos
    ltrecii
    mpbi
    a1i
    lelttrd
    adantr
    stoweidlem62
    pm2.61dan
    wph
    @10
    @13
    vf
    cA
    wph
    @25
    wa
    #
    @9
    @12
    vt
    cT
    wph
    @25
    vt
    stoweid.2
    @25
    vt
    nfv
    nfan
    @43
    @30
    wa
    #
    @9
    @8
    cE
    cle
    wbr
    #
    @12
    wph
    @45
    @25
    @30
    wph
    @38
    @39
    @45
    @40
    @41
    cE
    @6
    xrmin1
    syl2anc
    ad2antrr
    @44
    @5
    cr
    wcel
    @8
    cr
    wcel
    #
    cE
    cr
    wcel
    #
    @9
    @45
    wa
    @12
    wi
    @44
    @4
    @44
    @2
    @3
    @44
    cT
    cr
    @1
    wf
    #
    @30
    wa
    @2
    cr
    wcel
    @2
    cc
    wcel
    @44
    @48
    @30
    @44
    cC
    cT
    @1
    cJ
    cK
    stoweid.3
    stoweid.5
    stoweid.6
    @44
    cA
    cC
    @1
    wph
    @24
    @25
    @30
    stoweid.7
    ad2antrr
    wph
    @25
    @30
    simplr
    sseldd
    fcnre
    @43
    @30
    simpr
    #
    jca
    cT
    cr
    @0
    @1
    ffvelrn
    @2
    recn
    3syl
    @44
    cT
    cr
    cF
    wf
    #
    @30
    wa
    @3
    cr
    wcel
    @3
    cc
    wcel
    @44
    @50
    @30
    @44
    cC
    cT
    cF
    cJ
    cK
    stoweid.3
    stoweid.5
    stoweid.6
    wph
    @32
    @25
    @30
    stoweid.12
    ad2antrr
    fcnre
    @49
    jca
    cT
    cr
    @0
    cF
    ffvelrn
    @3
    recn
    3syl
    subcld
    abscld
    wph
    @46
    @25
    @30
    wph
    @7
    cE
    @6
    cr
    @35
    @20
    c4
    cr
    wcel
    #
    c4
    cc0
    wne
    #
    w3a
    @36
    wph
    @20
    @51
    @52
    1re
    4re
    4ne0
    3pm3.2i
    c1
    c4
    redivcl
    mp1i
    ifcld
    ad2antrr
    wph
    @47
    @25
    @30
    @35
    ad2antrr
    @5
    @8
    cE
    ltletr
    syl3anc
    mpan2d
    ralimdaa
    reximdva
    mpd
end
