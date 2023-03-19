include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cexp.mm"
include "cmin.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "wo.mm"
include "wi.mm"
include "cn.mm"
include "wral.mm"
include "cz.mm"
include "wne.mm"
include "wa.mm"
include "crp.mm"
include "wrex.mm"
include "aalioulem2.mm"
include "aalioulem5.mm"
include "reeanv.mm"
include "sylanbrc.mm"
include "wcel.mm"
include "r19.26-2.mm"
include "cif.mm"
include "ifcl.mm"
include "adantl.mm"
include "simpr.mm"
include "cr.mm"
include "w3a.mm"
include "ad2antlr.mm"
include "nnrp.mm"
include "ad2antll.mm"
include "ad2antrr.mm"
include "nnzd.mm"
include "rpexpcld.mm"
include "rpdivcld.mm"
include "rpred.mm"
include "simplrl.mm"
include "cq.mm"
include "znq.mm"
include "qre.mm"
include "syl.mm"
include "resubcld.mm"
include "recnd.mm"
include "abscld.mm"
include "3jca.mm"
include "adantr.mm"
include "simplrr.mm"
include "min1.mm"
include "syl2anc.mm"
include "lediv1dd.mm"
include "anim1i.mm"
include "letr.mm"
include "sylc.mm"
include "ex.mm"
include "orim2d.mm"
include "embantd.mm"
include "adantrd.mm"
include "min2.mm"
include "adantld.mm"
include "pm2.61dane.mm"
include "ralimdvva.mm"
include "oveq1.mm"
include "breq1d.mm"
include "orbi2d.mm"
include "2ralbidv.mm"
include "rspcev.mm"
include "syl6an.mm"
include "syl5bir.mm"
include "rexlimdvva.mm"
include "mpd.mm"

theorem aalioulem6
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
  disjoint N x
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
  disjoint N a
  disjoint N b
  assert |- ( ph -> E. x e. RR+ A. p e. ZZ A. q e. NN ( A = ( p / q ) \/ ( x / ( q ^ N ) ) <_ ( abs ` ( A - ( p / q ) ) ) ) )

  proof
    wph
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
    wceq
    #
    cA
    @2
    wceq
    #
    va
    cv
    #
    @1
    cN
    cexp
    co
    #
    cdiv
    co
    #
    cA
    @2
    cmin
    co
    #
    cabs
    cfv
    #
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
    @3
    cc0
    wne
    #
    @5
    vb
    cv
    #
    @7
    cdiv
    co
    #
    @10
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
    wa
    #
    vb
    crp
    wrex
    va
    crp
    wrex
    #
    @5
    vx
    cv
    #
    @7
    cdiv
    co
    #
    @10
    cle
    wbr
    #
    wo
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
    #
    wph
    @14
    va
    crp
    wrex
    @21
    vb
    crp
    wrex
    @23
    wph
    va
    cA
    cF
    cN
    vq
    vp
    aalioulem2.a
    aalioulem2.b
    aalioulem2.c
    aalioulem2.d
    aalioulem2
    wph
    vb
    cA
    cF
    cN
    vq
    vp
    aalioulem2.a
    aalioulem2.b
    aalioulem2.c
    aalioulem2.d
    aalioulem3.e
    aalioulem5
    @14
    @21
    va
    vb
    crp
    crp
    reeanv
    sylanbrc
    wph
    @22
    @29
    va
    vb
    crp
    crp
    @22
    @13
    @20
    wa
    #
    vq
    cn
    wral
    vp
    cz
    wral
    #
    wph
    @6
    crp
    wcel
    #
    @16
    crp
    wcel
    #
    wa
    #
    wa
    #
    @29
    @13
    @20
    vp
    vq
    cz
    cn
    r19.26-2
    @35
    @6
    @16
    cle
    wbr
    #
    @6
    @16
    cif
    #
    crp
    wcel
    #
    @31
    @5
    @37
    @7
    cdiv
    co
    #
    @10
    cle
    wbr
    #
    wo
    #
    vq
    cn
    wral
    vp
    cz
    wral
    #
    @29
    @34
    @38
    wph
    @36
    @6
    @16
    crp
    ifcl
    #
    adantl
    @35
    @30
    @41
    vp
    vq
    cz
    cn
    @35
    @0
    cz
    wcel
    #
    @1
    cn
    wcel
    #
    wa
    #
    wa
    #
    @30
    @41
    wi
    @3
    cc0
    @47
    @4
    wa
    #
    @13
    @41
    @20
    @48
    @4
    @12
    @41
    @47
    @4
    simpr
    @48
    @11
    @40
    @5
    @47
    @11
    @40
    wi
    @4
    @47
    @11
    @40
    @47
    @11
    wa
    @39
    cr
    wcel
    #
    @8
    cr
    wcel
    #
    @10
    cr
    wcel
    #
    w3a
    #
    @39
    @8
    cle
    wbr
    #
    @11
    wa
    @40
    @47
    @52
    @11
    @47
    @49
    @50
    @51
    @47
    @39
    @47
    @37
    @7
    @34
    @38
    wph
    @46
    @43
    ad2antlr
    #
    @47
    @1
    cN
    @45
    @1
    crp
    wcel
    @35
    @44
    @1
    nnrp
    ad2antll
    @47
    cN
    wph
    cN
    cn
    wcel
    @34
    @46
    aalioulem2.c
    ad2antrr
    nnzd
    rpexpcld
    #
    rpdivcld
    rpred
    #
    @47
    @8
    @47
    @6
    @7
    wph
    @32
    @33
    @46
    simplrl
    #
    @55
    rpdivcld
    rpred
    @47
    @9
    @47
    @9
    @47
    cA
    @2
    wph
    cA
    cr
    wcel
    @34
    @46
    aalioulem2.d
    ad2antrr
    @46
    @2
    cr
    wcel
    #
    @35
    @46
    @2
    cq
    wcel
    @58
    @0
    @1
    znq
    @2
    qre
    syl
    adantl
    resubcld
    recnd
    abscld
    #
    3jca
    adantr
    @47
    @53
    @11
    @47
    @37
    @6
    @7
    @47
    @37
    @54
    rpred
    #
    @47
    @6
    @57
    rpred
    #
    @55
    @47
    @6
    cr
    wcel
    #
    @16
    cr
    wcel
    #
    @37
    @6
    cle
    wbr
    @61
    @47
    @16
    wph
    @32
    @33
    @46
    simplrr
    #
    rpred
    #
    @6
    @16
    min1
    syl2anc
    lediv1dd
    anim1i
    @39
    @8
    @10
    letr
    sylc
    ex
    adantr
    orim2d
    embantd
    adantrd
    @47
    @15
    wa
    #
    @20
    @41
    @13
    @66
    @15
    @19
    @41
    @47
    @15
    simpr
    @66
    @18
    @40
    @5
    @47
    @18
    @40
    wi
    @15
    @47
    @18
    @40
    @47
    @18
    wa
    @49
    @17
    cr
    wcel
    #
    @51
    w3a
    #
    @39
    @17
    cle
    wbr
    #
    @18
    wa
    @40
    @47
    @68
    @18
    @47
    @49
    @67
    @51
    @56
    @47
    @17
    @47
    @16
    @7
    @64
    @55
    rpdivcld
    rpred
    @59
    3jca
    adantr
    @47
    @69
    @18
    @47
    @37
    @16
    @7
    @60
    @65
    @55
    @47
    @62
    @63
    @37
    @16
    cle
    wbr
    @61
    @65
    @6
    @16
    min2
    syl2anc
    lediv1dd
    anim1i
    @39
    @17
    @10
    letr
    sylc
    ex
    adantr
    orim2d
    embantd
    adantld
    pm2.61dane
    ralimdvva
    @28
    @42
    vx
    @37
    crp
    @24
    @37
    wceq
    #
    @27
    @41
    vp
    vq
    cz
    cn
    @70
    @26
    @40
    @5
    @70
    @25
    @39
    @10
    cle
    @24
    @37
    @7
    cdiv
    oveq1
    breq1d
    orbi2d
    2ralbidv
    rspcev
    syl6an
    syl5bir
    rexlimdvva
    mpd
end
