include "cfv.mm"
include "climc.mm"
include "co.mm"
include "wcel.mm"
include "cc.mm"
include "cv.mm"
include "wne.mm"
include "cmin.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "cicc.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "ftc1lem3.mm"
include "cioo.mm"
include "sseldd.mm"
include "ffvelrnd.mm"
include "ccom.mm"
include "cxp.mm"
include "cres.mm"
include "cxmt.mm"
include "cmopn.mm"
include "ccnp.mm"
include "wss.mm"
include "cnxmet.mm"
include "cr.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "adantr.mm"
include "xmetres2.mm"
include "sylancr.mm"
include "a1i.mm"
include "crest.mm"
include "wceq.mm"
include "eqid.mm"
include "cnfldtopn.mm"
include "metrest.mm"
include "syl5eq.mm"
include "oveq1d.mm"
include "fveq1d.mm"
include "eleqtrd.mm"
include "simpr.mm"
include "metcnpi2.mm"
include "syl22anc.mm"
include "ad2antrr.mm"
include "ovresd.mm"
include "sselda.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "ioossicc.mm"
include "sseldi.mm"
include "cnmetdval.mm"
include "eqtrd.mm"
include "breq1d.mm"
include "wf.mm"
include "ffvelrnda.mm"
include "imbi12d.mm"
include "ralbidva.mm"
include "simprll.mm"
include "eldifsni.mm"
include "syl.mm"
include "cle.mm"
include "cibl.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simprlr.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "rspccva.mm"
include "sylan.mm"
include "eldifad.mm"
include "simprr.mm"
include "ftc1lem5.mm"
include "mpdan.mm"
include "expr.mm"
include "adantld.mm"
include "ralrimdva.mm"
include "sylbid.mm"
include "anassrs.mm"
include "reximdva.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "cdiv.mm"
include "ftc1lem2.mm"
include "dvlem.mm"
include "fmptd.mm"
include "ssdifssd.mm"
include "ellimc3.mm"
include "mpbir2and.mm"

theorem ftc1lem6
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cL: class L
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vd: setvar d
  let vr: setvar r
  let ve: setvar e
  let cX: class X
  let cE: class E
  let cY: class Y
  let cR: class R
  assume ftc1.g: |- G = ( x e. ( A [,] B ) |-> S. ( A (,) x ) ( F ` t ) _d t )
  assume ftc1.a: |- ( ph -> A e. RR )
  assume ftc1.b: |- ( ph -> B e. RR )
  assume ftc1.le: |- ( ph -> A <_ B )
  assume ftc1.s: |- ( ph -> ( A (,) B ) C_ D )
  assume ftc1.d: |- ( ph -> D C_ RR )
  assume ftc1.i: |- ( ph -> F e. L^1 )
  assume ftc1.c: |- ( ph -> C e. ( A (,) B ) )
  assume ftc1.f: |- ( ph -> F e. ( ( K CnP L ) ` C ) )
  assume ftc1.j: |- J = ( L |`t RR )
  assume ftc1.k: |- K = ( L |`t D )
  assume ftc1.l: |- L = ( TopOpen ` CCfld )
  assume ftc1.h: |- H = ( z e. ( ( A [,] B ) \ { C } ) |-> ( ( ( G ` z ) - ( G ` C ) ) / ( z - C ) ) )

  disjoint t x
  disjoint t z
  disjoint C t
  disjoint x z
  disjoint C x
  disjoint C z
  disjoint D t
  disjoint D x
  disjoint D z
  disjoint G z
  disjoint A t
  disjoint A x
  disjoint A z
  disjoint B t
  disjoint B x
  disjoint B z
  disjoint ph t
  disjoint ph x
  disjoint ph z
  disjoint F t
  disjoint F x
  disjoint F z
  disjoint L x
  disjoint L z
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint C s
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t y
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint C u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint C v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint C w
  disjoint x y
  disjoint y z
  disjoint C y
  disjoint d r
  disjoint d s
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint D d
  disjoint r s
  disjoint r t
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint D r
  disjoint D s
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D y
  disjoint d e
  disjoint G d
  disjoint e r
  disjoint e s
  disjoint e u
  disjoint e y
  disjoint e z
  disjoint G e
  disjoint G r
  disjoint G s
  disjoint G u
  disjoint G y
  disjoint A d
  disjoint e t
  disjoint e v
  disjoint e w
  disjoint e x
  disjoint A e
  disjoint A r
  disjoint A s
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint A y
  disjoint B d
  disjoint B e
  disjoint B r
  disjoint B s
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B y
  disjoint X t
  disjoint X x
  disjoint X z
  disjoint E t
  disjoint E y
  disjoint H s
  disjoint H u
  disjoint H v
  disjoint H w
  disjoint H y
  disjoint d ph
  disjoint e ph
  disjoint ph r
  disjoint ph s
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint Y t
  disjoint Y x
  disjoint F d
  disjoint F r
  disjoint F s
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F y
  disjoint L s
  disjoint L u
  disjoint L v
  disjoint L w
  disjoint L y
  disjoint R y
  assert |- ( ph -> ( F ` C ) e. ( H limCC C ) )

  proof
    wph
    cC
    cF
    cfv
    #
    cH
    cC
    climc
    co
    wcel
    @0
    cc
    wcel
    #
    vs
    cv
    #
    cC
    wne
    #
    @2
    cC
    cmin
    co
    cabs
    cfv
    vv
    cv
    #
    clt
    wbr
    #
    wa
    @2
    cH
    cfv
    @0
    cmin
    co
    cabs
    cfv
    vw
    cv
    #
    clt
    wbr
    #
    wi
    #
    vs
    cA
    cB
    cicc
    co
    #
    cC
    csn
    #
    cdif
    #
    wral
    #
    vv
    crp
    wrex
    #
    vw
    crp
    wral
    wph
    cD
    cc
    cC
    cF
    wph
    vx
    vt
    cA
    cB
    cC
    cD
    cF
    cG
    cJ
    cK
    cL
    ftc1.g
    ftc1.a
    ftc1.b
    ftc1.le
    ftc1.s
    ftc1.d
    ftc1.i
    ftc1.c
    ftc1.f
    ftc1.j
    ftc1.k
    ftc1.l
    ftc1lem3
    #
    wph
    cA
    cB
    cioo
    co
    #
    cD
    cC
    ftc1.s
    ftc1.c
    sseldd
    #
    ffvelrnd
    #
    wph
    @13
    vw
    crp
    wph
    @6
    crp
    wcel
    #
    wa
    #
    vy
    cv
    #
    cC
    cabs
    cmin
    ccom
    #
    cD
    cD
    cxp
    cres
    #
    co
    #
    @4
    clt
    wbr
    #
    @20
    cF
    cfv
    #
    @0
    @21
    co
    #
    @6
    clt
    wbr
    #
    wi
    #
    vy
    cD
    wral
    #
    vv
    crp
    wrex
    #
    @13
    @19
    @22
    cD
    cxmt
    cfv
    wcel
    #
    @21
    cc
    cxmt
    cfv
    wcel
    #
    cF
    cC
    @22
    cmopn
    cfv
    #
    cL
    ccnp
    co
    #
    cfv
    #
    wcel
    #
    @18
    @30
    @19
    @32
    cD
    cc
    wss
    #
    @31
    cnxmet
    wph
    @37
    @18
    wph
    cD
    cr
    cc
    ftc1.d
    ax-resscn
    syl6ss
    #
    adantr
    @21
    cD
    cc
    xmetres2
    sylancr
    @32
    @19
    cnxmet
    a1i
    wph
    @36
    @18
    wph
    cF
    cC
    cK
    cL
    ccnp
    co
    #
    cfv
    #
    @35
    ftc1.f
    wph
    cC
    @39
    @34
    wph
    cK
    @33
    cL
    ccnp
    wph
    cK
    cL
    cD
    crest
    co
    #
    @33
    ftc1.k
    wph
    @32
    @37
    @41
    @33
    wceq
    cnxmet
    @38
    @21
    @22
    cL
    @33
    cc
    cD
    @22
    eqid
    cL
    ftc1.l
    cnfldtopn
    #
    @33
    eqid
    #
    metrest
    sylancr
    syl5eq
    oveq1d
    fveq1d
    eleqtrd
    adantr
    wph
    @18
    simpr
    vv
    vy
    @6
    @22
    @21
    cC
    cF
    @33
    cL
    cD
    cc
    @43
    @42
    metcnpi2
    syl22anc
    @19
    @29
    @12
    vv
    crp
    wph
    @18
    @4
    crp
    wcel
    #
    @29
    @12
    wi
    wph
    @18
    @44
    wa
    #
    wa
    #
    @29
    @20
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    @4
    clt
    wbr
    #
    @25
    @0
    cmin
    co
    #
    cabs
    cfv
    #
    @6
    clt
    wbr
    #
    wi
    #
    vy
    cD
    wral
    #
    @12
    @46
    @28
    @53
    vy
    cD
    @46
    @20
    cD
    wcel
    #
    wa
    #
    @24
    @49
    @27
    @52
    @56
    @23
    @48
    @4
    clt
    @56
    @23
    @20
    cC
    @21
    co
    #
    @48
    @56
    @20
    cC
    @21
    cD
    @46
    @55
    simpr
    wph
    cC
    cD
    wcel
    @45
    @55
    @16
    ad2antrr
    ovresd
    @56
    @20
    cc
    wcel
    cC
    cc
    wcel
    #
    @57
    @48
    wceq
    @46
    cD
    cc
    @20
    wph
    @37
    @45
    @38
    adantr
    sselda
    wph
    @58
    @45
    @55
    wph
    @9
    cc
    cC
    wph
    @9
    cr
    cc
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @9
    cr
    wss
    ftc1.a
    ftc1.b
    cA
    cB
    iccssre
    syl2anc
    ax-resscn
    syl6ss
    #
    wph
    @15
    @9
    cC
    cA
    cB
    ioossicc
    ftc1.c
    sseldi
    #
    sseldd
    #
    ad2antrr
    @20
    cC
    @21
    @21
    eqid
    #
    cnmetdval
    syl2anc
    eqtrd
    breq1d
    @56
    @26
    @51
    @6
    clt
    @56
    @25
    cc
    wcel
    @1
    @26
    @51
    wceq
    @46
    cD
    cc
    @20
    cF
    wph
    cD
    cc
    cF
    wf
    @45
    @14
    adantr
    ffvelrnda
    wph
    @1
    @45
    @55
    @17
    ad2antrr
    @25
    @0
    @21
    @64
    cnmetdval
    syl2anc
    breq1d
    imbi12d
    ralbidva
    @46
    @54
    @8
    vs
    @11
    @46
    @2
    @11
    wcel
    #
    @54
    @8
    @46
    @65
    @54
    wa
    #
    wa
    @5
    @7
    @3
    @46
    @66
    @5
    @7
    @46
    @66
    @5
    wa
    #
    wa
    #
    @3
    @7
    @68
    @65
    @3
    @46
    @65
    @54
    @5
    simprll
    #
    @2
    @9
    cC
    eldifsni
    syl
    @68
    vx
    vu
    vz
    vt
    cA
    cB
    cC
    cD
    @4
    @6
    cF
    cG
    cH
    cJ
    cK
    cL
    @2
    ftc1.g
    wph
    @59
    @45
    @67
    ftc1.a
    ad2antrr
    wph
    @60
    @45
    @67
    ftc1.b
    ad2antrr
    wph
    cA
    cB
    cle
    wbr
    @45
    @67
    ftc1.le
    ad2antrr
    wph
    @15
    cD
    wss
    @45
    @67
    ftc1.s
    ad2antrr
    wph
    cD
    cr
    wss
    @45
    @67
    ftc1.d
    ad2antrr
    wph
    cF
    cibl
    wcel
    @45
    @67
    ftc1.i
    ad2antrr
    wph
    cC
    @15
    wcel
    @45
    @67
    ftc1.c
    ad2antrr
    wph
    cF
    @40
    wcel
    @45
    @67
    ftc1.f
    ad2antrr
    ftc1.j
    ftc1.k
    ftc1.l
    ftc1.h
    wph
    @18
    @44
    @67
    simplrl
    wph
    @18
    @44
    @67
    simplrr
    @68
    @54
    vu
    cv
    #
    cD
    wcel
    @70
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    @4
    clt
    wbr
    #
    @70
    cF
    cfv
    #
    @0
    cmin
    co
    #
    cabs
    cfv
    #
    @6
    clt
    wbr
    #
    wi
    #
    @46
    @65
    @54
    @5
    simprlr
    @53
    @78
    vy
    @70
    cD
    @20
    @70
    wceq
    #
    @49
    @73
    @52
    @77
    @79
    @48
    @72
    @4
    clt
    @79
    @47
    @71
    cabs
    @20
    @70
    cC
    cmin
    oveq1
    fveq2d
    breq1d
    @79
    @51
    @76
    @6
    clt
    @79
    @50
    @75
    cabs
    @79
    @25
    @74
    @0
    cmin
    @20
    @70
    cF
    fveq2
    oveq1d
    fveq2d
    breq1d
    imbi12d
    rspccva
    sylan
    @68
    @2
    @9
    @10
    @69
    eldifad
    @46
    @66
    @5
    simprr
    ftc1lem5
    mpdan
    expr
    adantld
    expr
    ralrimdva
    sylbid
    anassrs
    reximdva
    mpd
    ralrimiva
    wph
    vw
    vv
    vs
    @11
    cC
    @0
    cH
    wph
    vz
    @11
    vz
    cv
    #
    cG
    cfv
    cC
    cG
    cfv
    cmin
    co
    @80
    cC
    cmin
    co
    cdiv
    co
    cc
    cH
    wph
    @80
    cC
    @9
    cG
    wph
    vx
    vt
    cA
    cB
    cD
    cF
    cG
    ftc1.g
    ftc1.a
    ftc1.b
    ftc1.le
    ftc1.s
    ftc1.d
    ftc1.i
    @14
    ftc1lem2
    @61
    @62
    dvlem
    ftc1.h
    fmptd
    wph
    @9
    cc
    @10
    @61
    ssdifssd
    @63
    ellimc3
    mpbir2and
end
