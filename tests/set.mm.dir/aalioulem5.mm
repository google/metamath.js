include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "cmin.mm"
include "cabs.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "cexp.mm"
include "wo.mm"
include "wi.mm"
include "cn.mm"
include "wral.mm"
include "cz.mm"
include "crp.mm"
include "wrex.mm"
include "aalioulem4.mm"
include "wcel.mm"
include "cif.mm"
include "simpr.mm"
include "1rp.mm"
include "ifcl.mm"
include "sylancl.mm"
include "clt.mm"
include "cr.mm"
include "w3a.mm"
include "adantr.mm"
include "simprr.mm"
include "nnrpd.mm"
include "ad2antrr.mm"
include "nnzd.mm"
include "rpexpcld.mm"
include "rpdivcld.mm"
include "rpred.mm"
include "1re.mm"
include "a1i.mm"
include "cq.mm"
include "znq.mm"
include "qre.mm"
include "syl.mm"
include "adantl.mm"
include "resubcld.mm"
include "recnd.mm"
include "abscld.mm"
include "3jca.mm"
include "rprecred.mm"
include "simplr.mm"
include "min2.mm"
include "lediv1dd.mm"
include "cmul.mm"
include "nnnn0d.mm"
include "nnexpcld.mm"
include "1nn.mm"
include "nnmulcld.mm"
include "nnge1d.mm"
include "ledivmuld.mm"
include "mpbird.mm"
include "letrd.mm"
include "ltle.mm"
include "sylancr.mm"
include "imp.mm"
include "jca.mm"
include "letr.mm"
include "sylc.mm"
include "olcd.mm"
include "2a1d.mm"
include "pm3.21.mm"
include "min1.mm"
include "anim1i.mm"
include "ex.mm"
include "orim2d.mm"
include "imim12d.mm"
include "ltlecasei.mm"
include "ralimdvva.mm"
include "oveq1.mm"
include "breq1d.mm"
include "orbi2d.mm"
include "imbi2d.mm"
include "2ralbidv.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem aalioulem5
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
  assert |- ( ph -> E. x e. RR+ A. p e. ZZ A. q e. NN ( ( F ` ( p / q ) ) =/= 0 -> ( A = ( p / q ) \/ ( x / ( q ^ N ) ) <_ ( abs ` ( A - ( p / q ) ) ) ) ) )

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
    cc0
    wne
    #
    cA
    @2
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
    @5
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
    va
    crp
    wrex
    @3
    @8
    vx
    cv
    #
    @10
    cdiv
    co
    #
    @5
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
    #
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
    aalioulem3.e
    aalioulem4
    wph
    @15
    @22
    va
    crp
    wph
    @9
    crp
    wcel
    #
    wa
    #
    @9
    c1
    cle
    wbr
    #
    @9
    c1
    cif
    #
    crp
    wcel
    #
    @15
    @3
    @8
    @26
    @10
    cdiv
    co
    #
    @5
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
    @22
    @24
    @23
    c1
    crp
    wcel
    @27
    wph
    @23
    simpr
    1rp
    @25
    @9
    c1
    crp
    ifcl
    sylancl
    #
    @24
    @14
    @31
    vp
    vq
    cz
    cn
    @24
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
    @14
    @31
    wi
    c1
    @5
    @37
    c1
    @5
    clt
    wbr
    #
    wa
    #
    @30
    @14
    @3
    @39
    @29
    @8
    @39
    @28
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    w3a
    #
    @28
    c1
    cle
    wbr
    #
    c1
    @5
    cle
    wbr
    #
    wa
    @29
    @37
    @43
    @38
    @37
    @40
    @41
    @42
    @37
    @28
    @37
    @26
    @10
    @24
    @27
    @36
    @33
    adantr
    #
    @37
    @1
    cN
    @37
    @1
    @24
    @34
    @35
    simprr
    #
    nnrpd
    @37
    cN
    wph
    cN
    cn
    wcel
    @23
    @36
    aalioulem2.c
    ad2antrr
    #
    nnzd
    rpexpcld
    #
    rpdivcld
    rpred
    #
    @41
    @37
    1re
    a1i
    #
    @37
    @4
    @37
    @4
    @37
    cA
    @2
    wph
    cA
    cr
    wcel
    @23
    @36
    aalioulem2.d
    ad2antrr
    @36
    @2
    cr
    wcel
    #
    @24
    @36
    @2
    cq
    wcel
    @52
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
    @39
    @44
    @45
    @37
    @44
    @38
    @37
    @28
    c1
    @10
    cdiv
    co
    #
    c1
    @50
    @37
    @10
    @49
    rprecred
    @51
    @37
    @26
    c1
    @10
    @37
    @26
    @46
    rpred
    #
    @51
    @49
    @37
    @9
    cr
    wcel
    #
    @41
    @26
    c1
    cle
    wbr
    @37
    @9
    wph
    @23
    @36
    simplr
    #
    rpred
    #
    1re
    @9
    c1
    min2
    sylancl
    lediv1dd
    @37
    @54
    c1
    cle
    wbr
    c1
    @10
    c1
    cmul
    co
    #
    cle
    wbr
    @37
    @59
    @37
    @10
    c1
    @37
    @1
    cN
    @47
    @37
    cN
    @48
    nnnn0d
    nnexpcld
    c1
    cn
    wcel
    @37
    1nn
    a1i
    nnmulcld
    nnge1d
    @37
    c1
    c1
    @10
    @51
    @51
    @49
    ledivmuld
    mpbird
    letrd
    adantr
    @37
    @38
    @45
    @37
    @41
    @42
    @38
    @45
    wi
    1re
    @53
    c1
    @5
    ltle
    sylancr
    imp
    jca
    @28
    c1
    @5
    letr
    sylc
    olcd
    2a1d
    @37
    @6
    wa
    #
    @3
    @7
    @13
    @30
    @6
    @3
    @7
    wi
    @37
    @6
    @3
    pm3.21
    adantl
    @60
    @12
    @29
    @8
    @37
    @12
    @29
    wi
    @6
    @37
    @12
    @29
    @37
    @12
    wa
    @40
    @11
    cr
    wcel
    #
    @42
    w3a
    #
    @28
    @11
    cle
    wbr
    #
    @12
    wa
    @29
    @37
    @62
    @12
    @37
    @40
    @61
    @42
    @50
    @37
    @11
    @37
    @9
    @10
    @57
    @49
    rpdivcld
    rpred
    @53
    3jca
    adantr
    @37
    @63
    @12
    @37
    @26
    @9
    @10
    @55
    @58
    @49
    @37
    @56
    @41
    @26
    @9
    cle
    wbr
    @58
    1re
    @9
    c1
    min1
    sylancl
    lediv1dd
    anim1i
    @28
    @11
    @5
    letr
    sylc
    ex
    adantr
    orim2d
    imim12d
    @51
    @53
    ltlecasei
    ralimdvva
    @21
    @32
    vx
    @26
    crp
    @16
    @26
    wceq
    #
    @20
    @31
    vp
    vq
    cz
    cn
    @64
    @19
    @30
    @3
    @64
    @18
    @29
    @8
    @64
    @17
    @28
    @5
    cle
    @16
    @26
    @10
    cdiv
    oveq1
    breq1d
    orbi2d
    imbi2d
    2ralbidv
    rspcev
    syl6an
    rexlimdva
    mpd
end
