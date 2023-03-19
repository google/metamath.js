include "csn.mm"
include "ccda.mm"
include "co.mm"
include "ccnv.mm"
include "cfv.mm"
include "cop.mm"
include "crn.mm"
include "wcel.mm"
include "wceq.mm"
include "df-ov.mm"
include "xpsfval.mm"
include "syl2anc.mm"
include "syl5eqr.mm"
include "cxp.mm"
include "opelxpi.mm"
include "wf1o.mm"
include "wf.mm"
include "xpsff1o2.mm"
include "f1of.mm"
include "ax-mp.mm"
include "ffvelrni.mm"
include "syl.mm"
include "eqeltrrd.mm"
include "mpd3an23.mm"
include "wi.mm"
include "f1ocnvfv.mm"
include "sylancr.mm"
include "mpd.mm"
include "oveq12d.mm"
include "c2o.mm"
include "cv.mm"
include "cmpt.mm"
include "wfn.mm"
include "cbs.mm"
include "xpscfn.mm"
include "csca.mm"
include "eqid.mm"
include "xpslem.mm"
include "eleqtrd.mm"
include "syl3anc.mm"
include "dffn5.mm"
include "sylib.mm"
include "wa.mm"
include "c0.mm"
include "cif.mm"
include "iftrue.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "oveq123d.mm"
include "eqtr4d.mm"
include "wn.mm"
include "iffalse.mm"
include "pm2.61i.mm"
include "adantr.mm"
include "simpr.mm"
include "xpscfv.mm"
include "3eqtr4a.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"

theorem xpsaddlem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let c.xb: class .xb
  let cT: class T
  let c.x: class .x.
  let c.xp: class .X.
  let cU: class U
  let vk: setvar k
  let cE: class E
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vs: setvar s
  let vc: setvar c
  let vd: setvar d
  let cG: class G
  let va: setvar a
  let vb: setvar b
  assume xpsval.t: |- T = ( R Xs. S )
  assume xpsval.x: |- X = ( Base ` R )
  assume xpsval.y: |- Y = ( Base ` S )
  assume xpsval.1: |- ( ph -> R e. V )
  assume xpsval.2: |- ( ph -> S e. W )
  assume xpsadd.3: |- ( ph -> A e. X )
  assume xpsadd.4: |- ( ph -> B e. Y )
  assume xpsadd.5: |- ( ph -> C e. X )
  assume xpsadd.6: |- ( ph -> D e. Y )
  assume xpsadd.7: |- ( ph -> ( A .x. C ) e. X )
  assume xpsadd.8: |- ( ph -> ( B .X. D ) e. Y )
  assume xpsaddlem.m: |- .x. = ( E ` R )
  assume xpsaddlem.n: |- .X. = ( E ` S )
  assume xpsaddlem.p: |- .xb = ( E ` T )
  assume xpsaddlem.f: |- F = ( x e. X , y e. Y |-> `' ( { x } +c { y } ) )
  assume xpsaddlem.u: |- U = ( ( Scalar ` R ) Xs_ `' ( { R } +c { S } ) )
  assume xpsaddlem.1: |- ( ( ph /\ `' ( { A } +c { B } ) e. ran F /\ `' ( { C } +c { D } ) e. ran F ) -> ( ( `' F ` `' ( { A } +c { B } ) ) .xb ( `' F ` `' ( { C } +c { D } ) ) ) = ( `' F ` ( `' ( { A } +c { B } ) ( E ` U ) `' ( { C } +c { D } ) ) ) )
  assume xpsaddlem.2: |- ( ( `' ( { R } +c { S } ) Fn 2o /\ `' ( { A } +c { B } ) e. ( Base ` U ) /\ `' ( { C } +c { D } ) e. ( Base ` U ) ) -> ( `' ( { A } +c { B } ) ( E ` U ) `' ( { C } +c { D } ) ) = ( k e. 2o |-> ( ( `' ( { A } +c { B } ) ` k ) ( E ` ( `' ( { R } +c { S } ) ` k ) ) ( `' ( { C } +c { D } ) ` k ) ) ) )

  disjoint k x
  disjoint k y
  disjoint A k
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B k
  disjoint B x
  disjoint B y
  disjoint C k
  disjoint C x
  disjoint C y
  disjoint D k
  disjoint D x
  disjoint D y
  disjoint S k
  disjoint U k
  disjoint W x
  disjoint k ph
  disjoint .x. k
  disjoint .x. x
  disjoint .x. y
  disjoint .X. k
  disjoint .X. x
  disjoint .X. y
  disjoint X k
  disjoint X x
  disjoint X y
  disjoint R k
  disjoint R x
  disjoint Y k
  disjoint Y x
  disjoint Y y
  disjoint r s
  disjoint r y
  disjoint s y
  disjoint c k
  disjoint c x
  disjoint c y
  disjoint A c
  disjoint B c
  disjoint c d
  disjoint C c
  disjoint d k
  disjoint d x
  disjoint d y
  disjoint C d
  disjoint G k
  disjoint D c
  disjoint D d
  disjoint F r
  disjoint F s
  disjoint c r
  disjoint c s
  disjoint S c
  disjoint d r
  disjoint d s
  disjoint S d
  disjoint k r
  disjoint k s
  disjoint S r
  disjoint S s
  disjoint U r
  disjoint U s
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a k
  disjoint a ph
  disjoint b c
  disjoint b d
  disjoint b k
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint a x
  disjoint a y
  disjoint X a
  disjoint b x
  disjoint b y
  disjoint X b
  disjoint X c
  disjoint X d
  disjoint R c
  disjoint R d
  disjoint r x
  disjoint R r
  disjoint s x
  disjoint R s
  disjoint .xb a
  disjoint .xb b
  disjoint .xb c
  disjoint .xb d
  disjoint Y a
  disjoint Y b
  disjoint Y c
  disjoint Y d
  assert |- ( ph -> ( <. A , B >. .xb <. C , D >. ) = <. ( A .x. C ) , ( B .X. D ) >. )

  proof
    wph
    cA
    csn
    cB
    csn
    ccda
    co
    ccnv
    #
    cF
    ccnv
    #
    cfv
    #
    cC
    csn
    cD
    csn
    ccda
    co
    ccnv
    #
    @1
    cfv
    #
    c.xb
    co
    #
    @0
    @3
    cU
    cE
    cfv
    co
    #
    @1
    cfv
    #
    cA
    cB
    cop
    #
    cC
    cD
    cop
    #
    c.xb
    co
    cA
    cC
    c.x
    co
    #
    cB
    cD
    c.xp
    co
    #
    cop
    #
    wph
    @0
    cF
    crn
    #
    wcel
    @3
    @13
    wcel
    @5
    @7
    wceq
    wph
    @8
    cF
    cfv
    #
    @0
    @13
    wph
    @14
    cA
    cB
    cF
    co
    #
    @0
    cA
    cB
    cF
    df-ov
    wph
    cA
    cX
    wcel
    #
    cB
    cY
    wcel
    #
    @15
    @0
    wceq
    xpsadd.3
    xpsadd.4
    vx
    vy
    cX
    cY
    cF
    cA
    cB
    xpsaddlem.f
    xpsfval
    syl2anc
    syl5eqr
    #
    wph
    @8
    cX
    cY
    cxp
    #
    wcel
    #
    @14
    @13
    wcel
    wph
    @16
    @17
    @20
    xpsadd.3
    xpsadd.4
    cA
    cB
    cX
    cY
    opelxpi
    syl2anc
    #
    @19
    @13
    @8
    cF
    @19
    @13
    cF
    wf1o
    #
    @19
    @13
    cF
    wf
    vx
    vy
    cX
    cY
    cF
    xpsaddlem.f
    xpsff1o2
    #
    @19
    @13
    cF
    f1of
    ax-mp
    #
    ffvelrni
    syl
    eqeltrrd
    #
    wph
    @9
    cF
    cfv
    #
    @3
    @13
    wph
    @26
    cC
    cD
    cF
    co
    #
    @3
    cC
    cD
    cF
    df-ov
    wph
    cC
    cX
    wcel
    #
    cD
    cY
    wcel
    #
    @27
    @3
    wceq
    xpsadd.5
    xpsadd.6
    vx
    vy
    cX
    cY
    cF
    cC
    cD
    xpsaddlem.f
    xpsfval
    syl2anc
    syl5eqr
    #
    wph
    @9
    @19
    wcel
    #
    @26
    @13
    wcel
    wph
    @28
    @29
    @31
    xpsadd.5
    xpsadd.6
    cC
    cD
    cX
    cY
    opelxpi
    syl2anc
    #
    @19
    @13
    @9
    cF
    @24
    ffvelrni
    syl
    eqeltrrd
    #
    xpsaddlem.1
    mpd3an23
    wph
    @2
    @8
    @4
    @9
    c.xb
    wph
    @14
    @0
    wceq
    #
    @2
    @8
    wceq
    #
    @18
    wph
    @22
    @20
    @34
    @35
    wi
    @23
    @21
    @19
    @13
    @8
    @0
    cF
    f1ocnvfv
    sylancr
    mpd
    wph
    @26
    @3
    wceq
    #
    @4
    @9
    wceq
    #
    @30
    wph
    @22
    @31
    @36
    @37
    wi
    @23
    @32
    @19
    @13
    @9
    @3
    cF
    f1ocnvfv
    sylancr
    mpd
    oveq12d
    wph
    @7
    @10
    csn
    @11
    csn
    ccda
    co
    ccnv
    #
    @1
    cfv
    #
    @12
    wph
    @6
    @38
    @1
    wph
    @6
    vk
    c2o
    vk
    cv
    #
    @0
    cfv
    #
    @40
    @3
    cfv
    #
    @40
    cR
    csn
    cS
    csn
    ccda
    co
    ccnv
    #
    cfv
    #
    cE
    cfv
    #
    co
    #
    cmpt
    #
    @38
    wph
    @43
    c2o
    wfn
    #
    @0
    cU
    cbs
    cfv
    #
    wcel
    @3
    @49
    wcel
    @6
    @47
    wceq
    wph
    cR
    cV
    wcel
    #
    cS
    cW
    wcel
    #
    @48
    xpsval.1
    xpsval.2
    cR
    cS
    cV
    cW
    xpscfn
    syl2anc
    wph
    @0
    @13
    @49
    @25
    wph
    vx
    vy
    cR
    cS
    cT
    cU
    cF
    cR
    csca
    cfv
    #
    cV
    cW
    cX
    cY
    xpsval.t
    xpsval.x
    xpsval.y
    xpsval.1
    xpsval.2
    xpsaddlem.f
    @52
    eqid
    xpsaddlem.u
    xpslem
    #
    eleqtrd
    wph
    @3
    @13
    @49
    @33
    @53
    eleqtrd
    xpsaddlem.2
    syl3anc
    wph
    @38
    vk
    c2o
    @40
    @38
    cfv
    #
    cmpt
    #
    @47
    wph
    @38
    c2o
    wfn
    #
    @38
    @55
    wceq
    wph
    @10
    cX
    wcel
    #
    @11
    cY
    wcel
    #
    @56
    xpsadd.7
    xpsadd.8
    @10
    @11
    cX
    cY
    xpscfn
    syl2anc
    vk
    c2o
    @38
    dffn5
    sylib
    wph
    vk
    c2o
    @46
    @54
    wph
    @40
    c2o
    wcel
    #
    wa
    #
    @40
    c0
    wceq
    #
    cA
    cB
    cif
    #
    @61
    cC
    cD
    cif
    #
    @61
    cR
    cS
    cif
    #
    cE
    cfv
    #
    co
    #
    @61
    @10
    @11
    cif
    #
    @46
    @54
    @61
    @66
    @67
    wceq
    @61
    @66
    @10
    @67
    @61
    @62
    cA
    @63
    cC
    @65
    c.x
    @61
    @65
    cR
    cE
    cfv
    c.x
    @61
    @64
    cR
    cE
    @61
    cR
    cS
    iftrue
    fveq2d
    xpsaddlem.m
    syl6eqr
    @61
    cA
    cB
    iftrue
    @61
    cC
    cD
    iftrue
    oveq123d
    @61
    @10
    @11
    iftrue
    eqtr4d
    @61
    wn
    #
    @66
    @11
    @67
    @68
    @62
    cB
    @63
    cD
    @65
    c.xp
    @68
    @65
    cS
    cE
    cfv
    c.xp
    @68
    @64
    cS
    cE
    @61
    cR
    cS
    iffalse
    fveq2d
    xpsaddlem.n
    syl6eqr
    @61
    cA
    cB
    iffalse
    @61
    cC
    cD
    iffalse
    oveq123d
    @61
    @10
    @11
    iffalse
    eqtr4d
    pm2.61i
    @60
    @41
    @62
    @42
    @63
    @45
    @65
    @60
    @44
    @64
    cE
    @60
    @50
    @51
    @59
    @44
    @64
    wceq
    wph
    @50
    @59
    xpsval.1
    adantr
    wph
    @51
    @59
    xpsval.2
    adantr
    wph
    @59
    simpr
    #
    cR
    cS
    @40
    cV
    cW
    xpscfv
    syl3anc
    fveq2d
    @60
    @16
    @17
    @59
    @41
    @62
    wceq
    wph
    @16
    @59
    xpsadd.3
    adantr
    wph
    @17
    @59
    xpsadd.4
    adantr
    @69
    cA
    cB
    @40
    cX
    cY
    xpscfv
    syl3anc
    @60
    @28
    @29
    @59
    @42
    @63
    wceq
    wph
    @28
    @59
    xpsadd.5
    adantr
    wph
    @29
    @59
    xpsadd.6
    adantr
    @69
    cC
    cD
    @40
    cX
    cY
    xpscfv
    syl3anc
    oveq123d
    @60
    @57
    @58
    @59
    @54
    @67
    wceq
    wph
    @57
    @59
    xpsadd.7
    adantr
    wph
    @58
    @59
    xpsadd.8
    adantr
    @69
    @10
    @11
    @40
    cX
    cY
    xpscfv
    syl3anc
    3eqtr4a
    mpteq2dva
    eqtr4d
    eqtr4d
    fveq2d
    wph
    @12
    cF
    cfv
    #
    @38
    wceq
    #
    @39
    @12
    wceq
    #
    wph
    @70
    @10
    @11
    cF
    co
    #
    @38
    @10
    @11
    cF
    df-ov
    wph
    @57
    @58
    @73
    @38
    wceq
    xpsadd.7
    xpsadd.8
    vx
    vy
    cX
    cY
    cF
    @10
    @11
    xpsaddlem.f
    xpsfval
    syl2anc
    syl5eqr
    wph
    @22
    @12
    @19
    wcel
    #
    @71
    @72
    wi
    @23
    wph
    @57
    @58
    @74
    xpsadd.7
    xpsadd.8
    @10
    @11
    cX
    cY
    opelxpi
    syl2anc
    @19
    @13
    @12
    @38
    cF
    f1ocnvfv
    sylancr
    mpd
    eqtrd
    3eqtr3d
end
