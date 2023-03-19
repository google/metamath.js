include "cr.mm"
include "wss.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "ioossre.mm"
include "eqsstri.mm"
include "a1i.mm"
include "wf.mm"
include "cc.mm"
include "dvfsumrlimf.mm"
include "ax-resscn.mm"
include "fss.mm"
include "sylancl.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "supeq1i.mm"
include "wcel.mm"
include "wne.mm"
include "wceq.mm"
include "ressxr.mm"
include "sseldi.mm"
include "renepnfd.mm"
include "ioopnfsup.mm"
include "syl2anc.mm"
include "syl5eq.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cabs.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "cmin.mm"
include "cmpt.mm"
include "cc0.mm"
include "crli.mm"
include "rlimmptrcl.mm"
include "ralrimiva.mm"
include "rlim0.mm"
include "mpbid.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "cif.mm"
include "cico.mm"
include "wb.mm"
include "peano2re.mm"
include "syl.mm"
include "ifcld.mm"
include "adantr.mm"
include "rexico.mm"
include "elicopnf.mm"
include "simprbda.mm"
include "ltp1d.mm"
include "simplbda.mm"
include "maxle.mm"
include "syl3anc.mm"
include "simprd.mm"
include "ltletrd.mm"
include "elioopnf.mm"
include "mpbir2and.mm"
include "syl6eleqr.mm"
include "simpld.mm"
include "jca.mm"
include "adantlr.mm"
include "csb.mm"
include "simprrl.mm"
include "adantrr.mm"
include "leidd.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nffv.mm"
include "nfbr.mm"
include "nfim.mm"
include "breq2.mm"
include "csbeq1a.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "rspc.mm"
include "mpid.mm"
include "dvmptrecl.mm"
include "dvfsumrlimge0.mm"
include "elrege0.mm"
include "sylanbrc.mm"
include "expr.mm"
include "simprrr.mm"
include "nfel1.mm"
include "eleq1d.mm"
include "syl3c.mm"
include "sylib.mm"
include "absid.mm"
include "cz.mm"
include "cdv.mm"
include "pnfxr.mm"
include "w3a.mm"
include "3simpa.mm"
include "syl3an3.mm"
include "3adant1r.mm"
include "3adantr3.mm"
include "sstri.mm"
include "pnfge.mm"
include "dvfsumlem4.mm"
include "ffvelrnd.mm"
include "subcld.mm"
include "abscld.mm"
include "simprll.mm"
include "rpred.mm"
include "lelttr.mm"
include "mpand.mm"
include "sylbid.mm"
include "syld.mm"
include "anassrs.mm"
include "com23.mm"
include "ralrimdva.mm"
include "jctild.mm"
include "syldan.mm"
include "expimpd.mm"
include "reximdv2.mm"
include "sylbird.mm"
include "ralimdva.mm"
include "mpd.mm"
include "caucvgr.mm"

theorem dvfsumrlim
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let vk: setvar k
  let cG: class G
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vy: setvar y
  let vz: setvar z
  let vc: setvar c
  let ve: setvar e
  let vm: setvar m
  let cE: class E
  let cH: class H
  let cL: class L
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cY: class Y
  let cU: class U
  let cX: class X
  assume dvfsum.s: |- S = ( T (,) +oo )
  assume dvfsum.z: |- Z = ( ZZ>= ` M )
  assume dvfsum.m: |- ( ph -> M e. ZZ )
  assume dvfsum.d: |- ( ph -> D e. RR )
  assume dvfsum.md: |- ( ph -> M <_ ( D + 1 ) )
  assume dvfsum.t: |- ( ph -> T e. RR )
  assume dvfsum.a: |- ( ( ph /\ x e. S ) -> A e. RR )
  assume dvfsum.b1: |- ( ( ph /\ x e. S ) -> B e. V )
  assume dvfsum.b2: |- ( ( ph /\ x e. Z ) -> B e. RR )
  assume dvfsum.b3: |- ( ph -> ( RR _D ( x e. S |-> A ) ) = ( x e. S |-> B ) )
  assume dvfsum.c: |- ( x = k -> B = C )
  assume dvfsumrlim.l: |- ( ( ph /\ ( x e. S /\ k e. S ) /\ ( D <_ x /\ x <_ k ) ) -> C <_ B )
  assume dvfsumrlim.g: |- G = ( x e. S |-> ( sum_ k e. ( M ... ( |_ ` x ) ) C - A ) )
  assume dvfsumrlim.k: |- ( ph -> ( x e. S |-> B ) ~~>r 0 )

  disjoint B k
  disjoint C x
  disjoint k x
  disjoint D k
  disjoint D x
  disjoint k ph
  disjoint ph x
  disjoint S k
  disjoint S x
  disjoint M k
  disjoint M x
  disjoint T x
  disjoint Z x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint c e
  disjoint c k
  disjoint c m
  disjoint c y
  disjoint c z
  disjoint B c
  disjoint e k
  disjoint e m
  disjoint e y
  disjoint e z
  disjoint B e
  disjoint k m
  disjoint k y
  disjoint k z
  disjoint m y
  disjoint m z
  disjoint B m
  disjoint B y
  disjoint B z
  disjoint x z
  disjoint C z
  disjoint c x
  disjoint D c
  disjoint x y
  disjoint D y
  disjoint E x
  disjoint E y
  disjoint G c
  disjoint G e
  disjoint G y
  disjoint G z
  disjoint H m
  disjoint H y
  disjoint H z
  disjoint c ph
  disjoint e x
  disjoint e ph
  disjoint m x
  disjoint m ph
  disjoint ph y
  disjoint S c
  disjoint S e
  disjoint S m
  disjoint S y
  disjoint S z
  disjoint L y
  disjoint M z
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint T c
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u z
  disjoint T u
  disjoint v w
  disjoint v x
  disjoint v z
  disjoint T v
  disjoint w x
  disjoint w z
  disjoint T w
  disjoint T z
  disjoint Y k
  disjoint Y m
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint U k
  disjoint U x
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint X k
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint X m
  disjoint u y
  disjoint X u
  disjoint v y
  disjoint X v
  disjoint w y
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ph -> G e. dom ~~>r )

  proof
    wph
    ve
    cS
    vc
    vy
    cG
    cS
    cr
    wss
    #
    wph
    cS
    cT
    cpnf
    cioo
    co
    #
    cr
    dvfsum.s
    cT
    cpnf
    ioossre
    eqsstri
    #
    a1i
    #
    wph
    cS
    cr
    cG
    wf
    cr
    cc
    wss
    cS
    cc
    cG
    wf
    #
    wph
    vx
    cA
    cB
    cC
    cD
    cS
    cT
    vk
    cG
    cM
    cV
    cZ
    dvfsum.s
    dvfsum.z
    dvfsum.m
    dvfsum.d
    dvfsum.md
    dvfsum.t
    dvfsum.a
    dvfsum.b1
    dvfsum.b2
    dvfsum.b3
    dvfsum.c
    dvfsumrlim.g
    dvfsumrlimf
    ax-resscn
    cS
    cr
    cc
    cG
    fss
    sylancl
    #
    wph
    cS
    cxr
    clt
    csup
    @1
    cxr
    clt
    csup
    #
    cpnf
    cxr
    cS
    @1
    clt
    dvfsum.s
    supeq1i
    wph
    cT
    cxr
    wcel
    #
    cT
    cpnf
    wne
    @6
    cpnf
    wceq
    wph
    cr
    cxr
    cT
    ressxr
    dvfsum.t
    sseldi
    #
    wph
    cT
    dvfsum.t
    renepnfd
    cT
    ioopnfsup
    syl2anc
    syl5eq
    wph
    vc
    cv
    #
    vx
    cv
    #
    cle
    wbr
    #
    cB
    cabs
    cfv
    #
    ve
    cv
    #
    clt
    wbr
    #
    wi
    #
    vx
    cS
    wral
    #
    vc
    cr
    wrex
    #
    ve
    crp
    wral
    #
    @9
    vy
    cv
    #
    cle
    wbr
    #
    @19
    cG
    cfv
    #
    @9
    cG
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @13
    clt
    wbr
    #
    wi
    #
    vy
    cS
    wral
    #
    vc
    cS
    wrex
    #
    ve
    crp
    wral
    wph
    vx
    cS
    cB
    cmpt
    #
    cc0
    crli
    wbr
    @18
    dvfsumrlim.k
    wph
    ve
    vc
    vx
    cS
    cB
    wph
    cB
    cc
    wcel
    vx
    cS
    wph
    cS
    cB
    cc0
    vx
    cV
    dvfsum.b1
    dvfsumrlim.k
    rlimmptrcl
    ralrimiva
    @3
    rlim0
    mpbid
    wph
    @17
    @28
    ve
    crp
    wph
    @13
    crp
    wcel
    #
    wa
    #
    @17
    @16
    vc
    cD
    cT
    c1
    caddc
    co
    #
    cle
    wbr
    #
    @32
    cD
    cif
    #
    cpnf
    cico
    co
    #
    wrex
    #
    @28
    @31
    @0
    @34
    cr
    wcel
    #
    @36
    @17
    wb
    @0
    @31
    @2
    a1i
    wph
    @37
    @30
    wph
    @33
    @32
    cD
    cr
    wph
    cT
    cr
    wcel
    #
    @32
    cr
    wcel
    #
    dvfsum.t
    cT
    peano2re
    #
    syl
    dvfsum.d
    ifcld
    #
    adantr
    @14
    cS
    @34
    vc
    vx
    rexico
    syl2anc
    @31
    @16
    @27
    vc
    @35
    cS
    @31
    @9
    @35
    wcel
    #
    @16
    @9
    cS
    wcel
    #
    @27
    wa
    #
    @31
    @42
    @43
    cD
    @9
    cle
    wbr
    #
    wa
    #
    @16
    @44
    wi
    #
    wph
    @42
    @46
    @30
    wph
    @42
    wa
    #
    @43
    @45
    @48
    @9
    @1
    cS
    @48
    @9
    @1
    wcel
    #
    @9
    cr
    wcel
    #
    cT
    @9
    clt
    wbr
    #
    wph
    @42
    @50
    @34
    @9
    cle
    wbr
    #
    wph
    @37
    @42
    @50
    @52
    wa
    wb
    @41
    @34
    @9
    elicopnf
    syl
    #
    simprbda
    #
    @48
    cT
    @32
    @9
    wph
    @38
    @42
    dvfsum.t
    adantr
    #
    @48
    @38
    @39
    @55
    @40
    syl
    #
    @54
    @48
    cT
    @55
    ltp1d
    @48
    @45
    @32
    @9
    cle
    wbr
    #
    @48
    @52
    @45
    @57
    wa
    #
    wph
    @42
    @50
    @52
    @53
    simplbda
    @48
    cD
    cr
    wcel
    #
    @39
    @50
    @52
    @58
    wb
    wph
    @59
    @42
    dvfsum.d
    adantr
    @56
    @54
    cD
    @32
    @9
    maxle
    syl3anc
    mpbid
    #
    simprd
    ltletrd
    @48
    @7
    @49
    @50
    @51
    wa
    wb
    wph
    @7
    @42
    @8
    adantr
    cT
    @9
    elioopnf
    syl
    mpbir2and
    dvfsum.s
    syl6eleqr
    @48
    @45
    @57
    @60
    simpld
    jca
    adantlr
    wph
    @30
    @46
    @47
    wph
    @30
    @46
    wa
    #
    wa
    #
    @16
    @27
    @43
    @62
    @16
    @26
    vy
    cS
    @62
    @19
    cS
    wcel
    #
    wa
    @20
    @16
    @25
    @62
    @63
    @20
    @16
    @25
    wi
    #
    wph
    @61
    @63
    @20
    wa
    #
    @64
    wph
    @61
    @65
    wa
    #
    wa
    #
    @16
    vx
    @9
    cB
    csb
    #
    cabs
    cfv
    #
    @13
    clt
    wbr
    #
    @25
    @67
    @16
    @9
    @9
    cle
    wbr
    #
    @70
    @67
    @9
    @67
    cS
    cr
    @9
    @2
    wph
    @61
    @43
    @65
    wph
    @30
    @43
    @45
    simprrl
    #
    adantrr
    #
    sseldi
    leidd
    @67
    @43
    @16
    @71
    @70
    wi
    #
    wi
    @73
    @15
    @74
    vx
    @9
    cS
    @71
    @70
    vx
    @71
    vx
    nfv
    vx
    @69
    @13
    clt
    vx
    @68
    cabs
    vx
    cabs
    nfcv
    vx
    @9
    cB
    nfcsb1v
    #
    nffv
    vx
    clt
    nfcv
    vx
    @13
    nfcv
    nfbr
    nfim
    @10
    @9
    wceq
    #
    @11
    @71
    @14
    @70
    @10
    @9
    @9
    cle
    breq2
    @76
    @12
    @69
    @13
    clt
    @76
    cB
    @68
    cabs
    vx
    @9
    cB
    csbeq1a
    #
    fveq2d
    breq1d
    imbi12d
    rspc
    syl
    mpid
    @67
    @70
    @68
    @13
    clt
    wbr
    #
    @25
    @67
    @69
    @68
    @13
    clt
    @67
    @68
    cr
    wcel
    #
    cc0
    @68
    cle
    wbr
    #
    wa
    #
    @69
    @68
    wceq
    @67
    @68
    cc0
    cpnf
    cico
    co
    #
    wcel
    #
    @81
    @67
    @43
    cD
    @10
    cle
    wbr
    #
    cB
    @82
    wcel
    #
    wi
    #
    vx
    cS
    wral
    #
    @45
    @83
    @73
    wph
    @87
    @66
    wph
    @86
    vx
    cS
    wph
    @10
    cS
    wcel
    #
    @84
    @85
    wph
    @88
    @84
    wa
    wa
    cB
    cr
    wcel
    #
    cc0
    cB
    cle
    wbr
    #
    @85
    wph
    @88
    @89
    @84
    wph
    vx
    cA
    cB
    cS
    cV
    @3
    dvfsum.a
    dvfsum.b1
    dvfsum.b3
    dvmptrecl
    adantrr
    wph
    vx
    cA
    cB
    cC
    cD
    cS
    cT
    vk
    cG
    cM
    cV
    cZ
    dvfsum.s
    dvfsum.z
    dvfsum.m
    dvfsum.d
    dvfsum.md
    dvfsum.t
    dvfsum.a
    dvfsum.b1
    dvfsum.b2
    dvfsum.b3
    dvfsum.c
    dvfsumrlim.l
    dvfsumrlim.g
    dvfsumrlim.k
    dvfsumrlimge0
    #
    cB
    elrege0
    sylanbrc
    expr
    ralrimiva
    adantr
    wph
    @61
    @45
    @65
    wph
    @30
    @43
    @45
    simprrr
    adantrr
    #
    @86
    @45
    @83
    wi
    vx
    @9
    cS
    @45
    @83
    vx
    @45
    vx
    nfv
    vx
    @68
    @82
    @75
    nfel1
    nfim
    @76
    @84
    @45
    @85
    @83
    @10
    @9
    cD
    cle
    breq2
    @76
    cB
    @68
    @82
    @77
    eleq1d
    imbi12d
    rspc
    syl3c
    @68
    elrege0
    sylib
    #
    @68
    absid
    syl
    breq1d
    @67
    @24
    @68
    cle
    wbr
    #
    @78
    @25
    @67
    vx
    cA
    cB
    cC
    cD
    cS
    cT
    cpnf
    vk
    cG
    cM
    cV
    @9
    @19
    cZ
    dvfsum.s
    dvfsum.z
    wph
    cM
    cz
    wcel
    @66
    dvfsum.m
    adantr
    wph
    @59
    @66
    dvfsum.d
    adantr
    wph
    cM
    cD
    c1
    caddc
    co
    cle
    wbr
    @66
    dvfsum.md
    adantr
    wph
    @38
    @66
    dvfsum.t
    adantr
    wph
    @88
    cA
    cr
    wcel
    @66
    dvfsum.a
    adantlr
    wph
    @88
    cB
    cV
    wcel
    @66
    dvfsum.b1
    adantlr
    wph
    @10
    cZ
    wcel
    @89
    @66
    dvfsum.b2
    adantlr
    wph
    cr
    vx
    cS
    cA
    cmpt
    cdv
    co
    @29
    wceq
    @66
    dvfsum.b3
    adantr
    dvfsum.c
    cpnf
    cxr
    wcel
    @67
    pnfxr
    a1i
    wph
    @88
    vk
    cv
    #
    cS
    wcel
    wa
    #
    @84
    @10
    @95
    cle
    wbr
    #
    @95
    cpnf
    cle
    wbr
    #
    w3a
    #
    cC
    cB
    cle
    wbr
    #
    @66
    @99
    wph
    @96
    @84
    @97
    wa
    @100
    @84
    @97
    @98
    3simpa
    dvfsumrlim.l
    syl3an3
    3adant1r
    dvfsumrlim.g
    wph
    @88
    @84
    @10
    cpnf
    cle
    wbr
    #
    w3a
    @90
    @66
    wph
    @88
    @84
    @90
    @101
    @91
    3adantr3
    adantlr
    @73
    wph
    @61
    @63
    @20
    simprrl
    #
    @92
    wph
    @61
    @63
    @20
    simprrr
    @67
    @19
    cxr
    wcel
    @19
    cpnf
    cle
    wbr
    @67
    cS
    cxr
    @19
    cS
    cr
    cxr
    @2
    ressxr
    sstri
    @102
    sseldi
    @19
    pnfge
    syl
    dvfsumlem4
    @67
    @24
    cr
    wcel
    @79
    @13
    cr
    wcel
    @94
    @78
    wa
    @25
    wi
    @67
    @23
    @67
    @21
    @22
    @67
    cS
    cc
    @19
    cG
    wph
    @4
    @66
    @5
    adantr
    #
    @102
    ffvelrnd
    @67
    cS
    cc
    @9
    cG
    @103
    @73
    ffvelrnd
    subcld
    abscld
    @67
    @79
    @80
    @93
    simpld
    @67
    @13
    wph
    @30
    @46
    @65
    simprll
    rpred
    @24
    @68
    @13
    lelttr
    syl3anc
    mpand
    sylbid
    syld
    anassrs
    expr
    com23
    ralrimdva
    @72
    jctild
    anassrs
    syldan
    expimpd
    reximdv2
    sylbird
    ralimdva
    mpd
    caucvgr
end
