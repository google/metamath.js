include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "wi.mm"
include "cr.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "cdiv.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "cexp.mm"
include "wo.mm"
include "cn.mm"
include "cz.mm"
include "aalioulem3.mm"
include "wcel.mm"
include "w3a.mm"
include "cq.mm"
include "simp2l.mm"
include "simp2r.mm"
include "znq.mm"
include "syl2anc.mm"
include "qre.mm"
include "syl.mm"
include "simp3r.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "breq12d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "com23.mm"
include "sylc.mm"
include "simp1r.mm"
include "nnrpd.mm"
include "simp1l.mm"
include "nnzd.mm"
include "rpexpcld.mm"
include "rpdivcld.mm"
include "rpred.mm"
include "adantr.mm"
include "cc.mm"
include "cply.mm"
include "wf.mm"
include "plyf.mm"
include "recnd.mm"
include "ffvelrnd.mm"
include "abscld.mm"
include "remulcld.mm"
include "resubcld.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "divrecd.mm"
include "absmuld.mm"
include "rpge0d.mm"
include "absidd.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "cdgr.mm"
include "mulcomd.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "aalioulem1.mm"
include "eqeltrd.mm"
include "simp3l.mm"
include "mulne0d.mm"
include "nnabscl.mm"
include "eqeltrrd.mm"
include "nnge1d.mm"
include "1red.mm"
include "ledivmuld.mm"
include "mpbird.mm"
include "rprecred.mm"
include "lemul2d.mm"
include "mpbid.mm"
include "eqbrtrd.mm"
include "simpr.mm"
include "letrd.mm"
include "olcd.mm"
include "ex.mm"
include "syld.mm"
include "3exp.mm"
include "com34.mm"
include "ralrimdvv.mm"
include "reximdva.mm"
include "mpd.mm"

theorem aalioulem4
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cN: class N
  let vq: setvar q
  let vp: setvar p
  let vr: setvar r
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume aalioulem2.a: |- N = ( deg ` F )
  assume aalioulem2.b: |- ( ph -> F e. ( Poly ` ZZ ) )
  assume aalioulem2.c: |- ( ph -> N e. NN )
  assume aalioulem2.d: |- ( ph -> A e. RR )
  assume aalioulem3.e: |- ( ph -> ( F ` A ) = 0 )

  disjoint ph x
  disjoint p ph
  disjoint ph q
  disjoint p x
  disjoint q x
  disjoint p q
  disjoint A x
  disjoint A p
  disjoint A q
  disjoint F x
  disjoint F p
  disjoint F q
  disjoint ph r
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint r x
  disjoint a x
  disjoint b x
  disjoint c x
  disjoint d x
  disjoint p r
  disjoint a p
  disjoint b p
  disjoint c p
  disjoint d p
  disjoint q r
  disjoint a q
  disjoint b q
  disjoint c q
  disjoint d q
  disjoint a r
  disjoint b r
  disjoint c r
  disjoint d r
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint b c
  disjoint b d
  disjoint c d
  disjoint A r
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A d
  disjoint F r
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F d
  assert |- ( ph -> E. x e. RR+ A. p e. ZZ A. q e. NN ( ( ( F ` ( p / q ) ) =/= 0 /\ ( abs ` ( A - ( p / q ) ) ) <_ 1 ) -> ( A = ( p / q ) \/ ( x / ( q ^ N ) ) <_ ( abs ` ( A - ( p / q ) ) ) ) ) )

  proof
    wph
    cA
    va
    cv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    c1
    cle
    wbr
    #
    vx
    cv
    #
    @0
    cF
    cfv
    #
    cabs
    cfv
    #
    cmul
    co
    #
    @2
    cle
    wbr
    #
    wi
    #
    va
    cr
    wral
    #
    vx
    crp
    wrex
    vp
    cv
    #
    vq
    cv
    #
    cdiv
    co
    #
    cF
    cfv
    #
    cc0
    wne
    #
    cA
    @13
    cmin
    co
    #
    cabs
    cfv
    #
    c1
    cle
    wbr
    #
    wa
    #
    cA
    @13
    wceq
    #
    @4
    @12
    cN
    cexp
    co
    #
    cdiv
    co
    #
    @17
    cle
    wbr
    #
    wo
    #
    wi
    #
    vq
    cn
    wral
    vp
    cz
    wral
    #
    vx
    crp
    wrex
    wph
    vx
    cA
    cF
    cN
    va
    aalioulem2.a
    aalioulem2.b
    aalioulem2.c
    aalioulem2.d
    aalioulem3.e
    aalioulem3
    wph
    @10
    @26
    vx
    crp
    wph
    @4
    crp
    wcel
    #
    wa
    #
    @10
    @25
    vp
    vq
    cz
    cn
    @28
    @11
    cz
    wcel
    #
    @12
    cn
    wcel
    #
    wa
    #
    @10
    @25
    @28
    @31
    @19
    @10
    @24
    @28
    @31
    @19
    @10
    @24
    wi
    @28
    @31
    @19
    w3a
    #
    @10
    @4
    @14
    cabs
    cfv
    #
    cmul
    co
    #
    @17
    cle
    wbr
    #
    @24
    @32
    @13
    cr
    wcel
    #
    @18
    @10
    @35
    wi
    @32
    @13
    cq
    wcel
    #
    @36
    @32
    @29
    @30
    @37
    @28
    @29
    @30
    @19
    simp2l
    #
    @28
    @29
    @30
    @19
    simp2r
    #
    @11
    @12
    znq
    syl2anc
    @13
    qre
    syl
    #
    @28
    @31
    @15
    @18
    simp3r
    @36
    @10
    @18
    @35
    @9
    @18
    @35
    wi
    va
    @13
    cr
    @0
    @13
    wceq
    #
    @3
    @18
    @8
    @35
    @41
    @2
    @17
    c1
    cle
    @41
    @1
    @16
    cabs
    @0
    @13
    cA
    cmin
    oveq2
    fveq2d
    #
    breq1d
    @41
    @7
    @34
    @2
    @17
    cle
    @41
    @6
    @33
    @4
    cmul
    @41
    @5
    @14
    cabs
    @0
    @13
    cF
    fveq2
    fveq2d
    oveq2d
    @42
    breq12d
    imbi12d
    rspcv
    com23
    sylc
    @32
    @35
    @24
    @32
    @35
    wa
    #
    @23
    @20
    @43
    @22
    @34
    @17
    @32
    @22
    cr
    wcel
    @35
    @32
    @22
    @32
    @4
    @21
    wph
    @27
    @31
    @19
    simp1r
    #
    @32
    @12
    cN
    @32
    @12
    @39
    nnrpd
    @32
    cN
    @32
    wph
    cN
    cn
    wcel
    wph
    @27
    @31
    @19
    simp1l
    #
    aalioulem2.c
    syl
    nnzd
    rpexpcld
    #
    rpdivcld
    rpred
    adantr
    @32
    @34
    cr
    wcel
    @35
    @32
    @4
    @33
    @32
    @4
    @44
    rpred
    @32
    @14
    @32
    cc
    cc
    @13
    cF
    @32
    cF
    cz
    cply
    cfv
    wcel
    #
    cc
    cc
    cF
    wf
    @32
    wph
    @47
    @45
    aalioulem2.b
    syl
    #
    cz
    cF
    plyf
    syl
    @32
    @13
    @40
    recnd
    ffvelrnd
    #
    abscld
    #
    remulcld
    adantr
    @32
    @17
    cr
    wcel
    @35
    @32
    @16
    @32
    @16
    @32
    cA
    @13
    @32
    wph
    cA
    cr
    wcel
    @45
    aalioulem2.d
    syl
    @40
    resubcld
    recnd
    abscld
    adantr
    @32
    @22
    @34
    cle
    wbr
    @35
    @32
    @22
    @4
    c1
    @21
    cdiv
    co
    #
    cmul
    co
    #
    @34
    cle
    @32
    @4
    @21
    @32
    @4
    @44
    rpcnd
    @32
    @21
    @46
    rpcnd
    #
    @32
    @21
    @46
    rpne0d
    #
    divrecd
    @32
    @51
    @33
    cle
    wbr
    #
    @52
    @34
    cle
    wbr
    @32
    @55
    c1
    @21
    @33
    cmul
    co
    #
    cle
    wbr
    @32
    @56
    @32
    @21
    @14
    cmul
    co
    #
    cabs
    cfv
    #
    @56
    cn
    @32
    @58
    @21
    cabs
    cfv
    #
    @33
    cmul
    co
    @56
    @32
    @21
    @14
    @53
    @49
    absmuld
    @32
    @59
    @21
    @33
    cmul
    @32
    @21
    @32
    @21
    @46
    rpred
    @32
    @21
    @46
    rpge0d
    absidd
    oveq1d
    eqtrd
    @32
    @57
    cz
    wcel
    @57
    cc0
    wne
    @58
    cn
    wcel
    @32
    @57
    @14
    @12
    cF
    cdgr
    cfv
    #
    cexp
    co
    #
    cmul
    co
    #
    cz
    @32
    @57
    @14
    @21
    cmul
    co
    @62
    @32
    @21
    @14
    @53
    @49
    mulcomd
    @21
    @61
    @14
    cmul
    cN
    @60
    @12
    cexp
    aalioulem2.a
    oveq2i
    oveq2i
    syl6eq
    @32
    cF
    @11
    @12
    @48
    @38
    @39
    aalioulem1
    eqeltrd
    @32
    @21
    @14
    @53
    @49
    @54
    @28
    @31
    @15
    @18
    simp3l
    mulne0d
    @57
    nnabscl
    syl2anc
    eqeltrrd
    nnge1d
    @32
    c1
    @33
    @21
    @32
    1red
    @50
    @46
    ledivmuld
    mpbird
    @32
    @51
    @33
    @4
    @32
    @21
    @46
    rprecred
    @50
    @44
    lemul2d
    mpbid
    eqbrtrd
    adantr
    @32
    @35
    simpr
    letrd
    olcd
    ex
    syld
    3exp
    com34
    com23
    ralrimdvv
    reximdva
    mpd
end
