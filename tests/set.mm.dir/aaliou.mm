include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "cexp.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wo.mm"
include "cn.mm"
include "wral.mm"
include "cz.mm"
include "crp.mm"
include "wrex.mm"
include "clt.mm"
include "aalioulem6.mm"
include "wcel.mm"
include "wa.mm"
include "c2.mm"
include "rphalfcl.mm"
include "adantl.mm"
include "cr.mm"
include "w3a.mm"
include "ad2antlr.mm"
include "nnrp.mm"
include "ad2antll.mm"
include "nnzd.mm"
include "ad2antrr.mm"
include "rpexpcld.mm"
include "rpdivcld.mm"
include "rpred.mm"
include "simplr.mm"
include "adantr.mm"
include "cq.mm"
include "znq.mm"
include "qre.mm"
include "syl.mm"
include "resubcl.mm"
include "syl2an.mm"
include "recnd.mm"
include "abscld.mm"
include "3jca.mm"
include "rpre.mm"
include "rphalflt.mm"
include "ltdiv1dd.mm"
include "anim1i.mm"
include "ex.mm"
include "ltletr.mm"
include "sylsyld.mm"
include "orim2d.mm"
include "ralimdvva.mm"
include "oveq1.mm"
include "breq1d.mm"
include "orbi2d.mm"
include "2ralbidv.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem aaliou
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
  assert |- ( ph -> E. x e. RR+ A. p e. ZZ A. q e. NN ( A = ( p / q ) \/ ( x / ( q ^ N ) ) < ( abs ` ( A - ( p / q ) ) ) ) )

  proof
    wph
    cA
    vp
    cv
    #
    vq
    cv
    #
    cdiv
    co
    #
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
    vx
    cv
    #
    @5
    cdiv
    co
    #
    @8
    clt
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
    aalioulem6
    wph
    @11
    @17
    va
    crp
    wph
    @4
    crp
    wcel
    #
    wa
    #
    @4
    c2
    cdiv
    co
    #
    crp
    wcel
    #
    @11
    @3
    @20
    @5
    cdiv
    co
    #
    @8
    clt
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
    @17
    @18
    @21
    wph
    @4
    rphalfcl
    #
    adantl
    @19
    @10
    @24
    vp
    vq
    cz
    cn
    @19
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
    @9
    @23
    @3
    @30
    @22
    cr
    wcel
    #
    @6
    cr
    wcel
    #
    @8
    cr
    wcel
    #
    w3a
    @9
    @22
    @6
    clt
    wbr
    #
    @9
    wa
    #
    @23
    @30
    @31
    @32
    @33
    @30
    @22
    @30
    @20
    @5
    @18
    @21
    wph
    @29
    @26
    ad2antlr
    #
    @30
    @1
    cN
    @28
    @1
    crp
    wcel
    @19
    @27
    @1
    nnrp
    ad2antll
    wph
    cN
    cz
    wcel
    @18
    @29
    wph
    cN
    aalioulem2.c
    nnzd
    ad2antrr
    rpexpcld
    #
    rpdivcld
    rpred
    @30
    @6
    @30
    @4
    @5
    wph
    @18
    @29
    simplr
    @37
    rpdivcld
    rpred
    @30
    @7
    @30
    @7
    @19
    cA
    cr
    wcel
    #
    @2
    cr
    wcel
    #
    @7
    cr
    wcel
    @29
    wph
    @38
    @18
    aalioulem2.d
    adantr
    @29
    @2
    cq
    wcel
    @39
    @0
    @1
    znq
    @2
    qre
    syl
    cA
    @2
    resubcl
    syl2an
    recnd
    abscld
    3jca
    @30
    @9
    @35
    @30
    @34
    @9
    @30
    @20
    @4
    @5
    @30
    @20
    @36
    rpred
    @18
    @4
    cr
    wcel
    wph
    @29
    @4
    rpre
    ad2antlr
    @37
    @18
    @20
    @4
    clt
    wbr
    wph
    @29
    @4
    rphalflt
    ad2antlr
    ltdiv1dd
    anim1i
    ex
    @22
    @6
    @8
    ltletr
    sylsyld
    orim2d
    ralimdvva
    @16
    @25
    vx
    @20
    crp
    @12
    @20
    wceq
    #
    @15
    @24
    vp
    vq
    cz
    cn
    @40
    @14
    @23
    @3
    @40
    @13
    @22
    @8
    clt
    @12
    @20
    @5
    cdiv
    oveq1
    breq1d
    orbi2d
    2ralbidv
    rspcev
    syl6an
    rexlimdva
    mpd
end
