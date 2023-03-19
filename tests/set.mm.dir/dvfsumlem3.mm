include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "csb.mm"
include "cmin.mm"
include "co.mm"
include "wa.mm"
include "cfl.mm"
include "c1.mm"
include "caddc.mm"
include "cr.mm"
include "cpnf.mm"
include "cioo.mm"
include "ioossre.mm"
include "eqsstri.mm"
include "sseldi.mm"
include "wcel.mm"
include "reflcl.mm"
include "peano2re.mm"
include "3syl.mm"
include "cz.mm"
include "adantr.mm"
include "cv.mm"
include "adantlr.mm"
include "cmpt.mm"
include "cdv.mm"
include "wceq.mm"
include "cxr.mm"
include "w3a.mm"
include "3adant1r.mm"
include "simpr.mm"
include "dvfsumlem2.mm"
include "wf.mm"
include "cmul.mm"
include "cfz.mm"
include "csu.mm"
include "wss.mm"
include "a1i.mm"
include "sselda.mm"
include "syl.mm"
include "resubcld.mm"
include "dvmptrecl.mm"
include "remulcld.mm"
include "fzfid.mm"
include "wral.mm"
include "ralrimiva.mm"
include "cuz.mm"
include "elfzuz.mm"
include "syl6eleqr.mm"
include "weq.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "syl2an.mm"
include "fsumrecl.mm"
include "readdcld.mm"
include "fmptd.mm"
include "ffvelrnd.mm"
include "clt.mm"
include "syl6eleq.mm"
include "wb.mm"
include "rexrd.mm"
include "elioopnf.mm"
include "mpbid.mm"
include "simprd.mm"
include "fllep1.mm"
include "ltletrd.mm"
include "flcld.mm"
include "peano2zd.mm"
include "flge.mm"
include "syl2anc.mm"
include "mpbir2and.mm"
include "letrd.mm"
include "flle.mm"
include "flidm.mm"
include "oveq1d.mm"
include "breqtrrd.mm"
include "simpld.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "elfzelz.mm"
include "adantl.mm"
include "zred.mm"
include "ad2antrr.mm"
include "elfzle1.mm"
include "lep1d.mm"
include "elfzle2.mm"
include "1red.mm"
include "leaddsub.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "xrletrd.mm"
include "flid.mm"
include "eqcomd.mm"
include "eqle.mm"
include "monoord2.mm"
include "leidd.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "csbeq1a.mm"
include "rspc.mm"
include "mpan9.mm"
include "csbeq1.mm"
include "rspcv.mm"
include "sylc.mm"
include "cvv.mm"
include "vex.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt3i.mm"
include "ax-mp.mm"
include "syldan.mm"
include "syl5eqel.mm"
include "3brtr4g.mm"
include "monoord.mm"
include "fvex.mm"
include "3brtr3g.mm"
include "jca.mm"
include "lecasei.mm"

theorem dvfsumlem3
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let cU: class U
  let vk: setvar k
  let cH: class H
  let cM: class M
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vy: setvar y
  let vz: setvar z
  let vc: setvar c
  let ve: setvar e
  let vm: setvar m
  let cE: class E
  let cG: class G
  let cL: class L
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
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
  assume dvfsum.u: |- ( ph -> U e. RR* )
  assume dvfsum.l: |- ( ( ph /\ ( x e. S /\ k e. S ) /\ ( D <_ x /\ x <_ k /\ k <_ U ) ) -> C <_ B )
  assume dvfsum.h: |- H = ( x e. S |-> ( ( ( x - ( |_ ` x ) ) x. B ) + ( sum_ k e. ( M ... ( |_ ` x ) ) C - A ) ) )
  assume dvfsumlem1.1: |- ( ph -> X e. S )
  assume dvfsumlem1.2: |- ( ph -> Y e. S )
  assume dvfsumlem1.3: |- ( ph -> D <_ X )
  assume dvfsumlem1.4: |- ( ph -> X <_ Y )
  assume dvfsumlem1.5: |- ( ph -> Y <_ U )

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
  disjoint Y k
  disjoint Y x
  disjoint Z x
  disjoint U k
  disjoint U x
  disjoint X k
  disjoint X x
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
  disjoint Y m
  disjoint Y y
  disjoint Y z
  disjoint k u
  disjoint k v
  disjoint k w
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
  disjoint X y
  disjoint X z
  assert |- ( ph -> ( ( H ` Y ) <_ ( H ` X ) /\ ( ( H ` X ) - [_ X / x ]_ B ) <_ ( ( H ` Y ) - [_ Y / x ]_ B ) ) )

  proof
    wph
    cY
    cH
    cfv
    #
    cX
    cH
    cfv
    #
    cle
    wbr
    #
    @1
    vx
    cX
    cB
    csb
    #
    cmin
    co
    #
    @0
    vx
    cY
    cB
    csb
    #
    cmin
    co
    #
    cle
    wbr
    #
    wa
    cY
    cX
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    wph
    cS
    cr
    cY
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
    dvfsumlem1.2
    sseldi
    #
    wph
    cX
    cr
    wcel
    #
    @8
    cr
    wcel
    #
    @9
    cr
    wcel
    #
    wph
    cS
    cr
    cX
    @11
    dvfsumlem1.1
    sseldi
    #
    cX
    reflcl
    #
    @8
    peano2re
    #
    3syl
    #
    wph
    cY
    @9
    cle
    wbr
    #
    wa
    vx
    cA
    cB
    cC
    cD
    cS
    cT
    cU
    vk
    cH
    cM
    cV
    cX
    cY
    cZ
    dvfsum.s
    dvfsum.z
    wph
    cM
    cz
    wcel
    #
    @20
    dvfsum.m
    adantr
    wph
    cD
    cr
    wcel
    #
    @20
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
    #
    @20
    dvfsum.md
    adantr
    wph
    cT
    cr
    wcel
    #
    @20
    dvfsum.t
    adantr
    wph
    vx
    cv
    #
    cS
    wcel
    #
    cA
    cr
    wcel
    #
    @20
    dvfsum.a
    adantlr
    wph
    @26
    cB
    cV
    wcel
    #
    @20
    dvfsum.b1
    adantlr
    wph
    @25
    cZ
    wcel
    #
    cB
    cr
    wcel
    #
    @20
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
    vx
    cS
    cB
    cmpt
    wceq
    #
    @20
    dvfsum.b3
    adantr
    dvfsum.c
    wph
    cU
    cxr
    wcel
    #
    @20
    dvfsum.u
    adantr
    wph
    @26
    vk
    cv
    #
    cS
    wcel
    wa
    #
    cD
    @25
    cle
    wbr
    @25
    @33
    cle
    wbr
    @33
    cU
    cle
    wbr
    w3a
    #
    cC
    cB
    cle
    wbr
    #
    @20
    dvfsum.l
    3adant1r
    dvfsum.h
    wph
    cX
    cS
    wcel
    #
    @20
    dvfsumlem1.1
    adantr
    wph
    cY
    cS
    wcel
    #
    @20
    dvfsumlem1.2
    adantr
    wph
    cD
    cX
    cle
    wbr
    #
    @20
    dvfsumlem1.3
    adantr
    wph
    cX
    cY
    cle
    wbr
    @20
    dvfsumlem1.4
    adantr
    wph
    cY
    cU
    cle
    wbr
    #
    @20
    dvfsumlem1.5
    adantr
    wph
    @20
    simpr
    dvfsumlem2
    wph
    @9
    cY
    cle
    wbr
    #
    wa
    #
    @2
    @7
    @42
    @0
    cY
    cfl
    cfv
    #
    cH
    cfv
    #
    @1
    @42
    cS
    cr
    cY
    cH
    wph
    cS
    cr
    cH
    wf
    #
    @41
    wph
    vx
    cS
    @25
    @25
    cfl
    cfv
    #
    cmin
    co
    #
    cB
    cmul
    co
    #
    cM
    @46
    cfz
    co
    #
    cC
    vk
    csu
    #
    cA
    cmin
    co
    #
    caddc
    co
    cr
    cH
    wph
    @26
    wa
    #
    @48
    @51
    @52
    @47
    cB
    @52
    @25
    @46
    wph
    cS
    cr
    @25
    cS
    cr
    wss
    wph
    @11
    a1i
    #
    sselda
    #
    @52
    @25
    cr
    wcel
    @46
    cr
    wcel
    @54
    @25
    reflcl
    syl
    resubcld
    wph
    vx
    cA
    cB
    cS
    cV
    @53
    dvfsum.a
    dvfsum.b1
    dvfsum.b3
    dvmptrecl
    #
    remulcld
    @52
    @50
    cA
    @52
    @49
    cC
    vk
    @52
    cM
    @46
    fzfid
    @52
    @30
    vx
    cZ
    wral
    #
    @33
    cZ
    wcel
    cC
    cr
    wcel
    #
    @33
    @49
    wcel
    #
    wph
    @56
    @26
    wph
    @30
    vx
    cZ
    dvfsum.b2
    ralrimiva
    adantr
    @58
    @33
    cM
    cuz
    cfv
    cZ
    @33
    cM
    @46
    elfzuz
    dvfsum.z
    syl6eleqr
    @30
    @57
    vx
    @33
    cZ
    vx
    vk
    weq
    cB
    cC
    cr
    dvfsum.c
    eleq1d
    rspccva
    syl2an
    fsumrecl
    dvfsum.a
    resubcld
    readdcld
    dvfsum.h
    fmptd
    adantr
    #
    wph
    @38
    @41
    dvfsumlem1.2
    adantr
    #
    ffvelrnd
    #
    @42
    cS
    cr
    @43
    cH
    @59
    @42
    @43
    @10
    cS
    @42
    @43
    @10
    wcel
    #
    @43
    cr
    wcel
    #
    cT
    @43
    clt
    wbr
    #
    @42
    cY
    cr
    wcel
    #
    @63
    wph
    @65
    @41
    @12
    adantr
    #
    cY
    reflcl
    #
    syl
    #
    @42
    cT
    @9
    @43
    wph
    @24
    @41
    dvfsum.t
    adantr
    #
    @42
    @13
    @14
    @15
    wph
    @13
    @41
    @16
    adantr
    #
    @17
    @18
    3syl
    #
    @68
    wph
    cT
    @9
    clt
    wbr
    #
    @41
    wph
    cT
    cX
    @9
    dvfsum.t
    @16
    @19
    wph
    @13
    cT
    cX
    clt
    wbr
    #
    wph
    cX
    @10
    wcel
    #
    @13
    @73
    wa
    #
    wph
    cX
    cS
    @10
    dvfsumlem1.1
    dvfsum.s
    syl6eleq
    wph
    cT
    cxr
    wcel
    #
    @74
    @75
    wb
    wph
    cT
    dvfsum.t
    rexrd
    #
    cT
    cX
    elioopnf
    syl
    mpbid
    simprd
    wph
    @13
    cX
    @9
    cle
    wbr
    #
    @16
    cX
    fllep1
    #
    syl
    ltletrd
    #
    adantr
    @42
    @41
    @9
    @43
    cle
    wbr
    #
    wph
    @41
    simpr
    @42
    @65
    @9
    cz
    wcel
    #
    @41
    @81
    wb
    @66
    @42
    @8
    @42
    cX
    @70
    flcld
    peano2zd
    #
    cY
    @9
    flge
    syl2anc
    mpbid
    #
    ltletrd
    @42
    @76
    @62
    @63
    @64
    wa
    wb
    wph
    @76
    @41
    @77
    adantr
    cT
    @43
    elioopnf
    syl
    mpbir2and
    dvfsum.s
    syl6eleqr
    #
    ffvelrnd
    #
    @42
    cS
    cr
    cX
    cH
    @59
    wph
    @37
    @41
    dvfsumlem1.1
    adantr
    #
    ffvelrnd
    #
    @42
    @0
    @44
    cle
    wbr
    #
    @44
    vx
    @43
    cB
    csb
    #
    cmin
    co
    #
    @6
    cle
    wbr
    #
    @42
    vx
    cA
    cB
    cC
    cD
    cS
    cT
    cU
    vk
    cH
    cM
    cV
    @43
    cY
    cZ
    dvfsum.s
    dvfsum.z
    wph
    @21
    @41
    dvfsum.m
    adantr
    #
    wph
    @22
    @41
    dvfsum.d
    adantr
    #
    wph
    @23
    @41
    dvfsum.md
    adantr
    #
    @69
    wph
    @26
    @27
    @41
    dvfsum.a
    adantlr
    #
    wph
    @26
    @28
    @41
    dvfsum.b1
    adantlr
    #
    wph
    @29
    @30
    @41
    dvfsum.b2
    adantlr
    #
    wph
    @31
    @41
    dvfsum.b3
    adantr
    #
    dvfsum.c
    wph
    @32
    @41
    dvfsum.u
    adantr
    #
    wph
    @34
    @35
    @36
    @41
    dvfsum.l
    3adant1r
    #
    dvfsum.h
    @85
    @60
    @42
    cD
    @9
    @43
    @94
    @71
    @68
    @42
    cD
    cX
    @9
    @94
    @70
    @71
    wph
    @39
    @41
    dvfsumlem1.3
    adantr
    #
    @42
    @13
    @78
    @70
    @79
    syl
    #
    letrd
    #
    @84
    letrd
    @42
    @65
    @43
    cY
    cle
    wbr
    @66
    cY
    flle
    syl
    #
    wph
    @40
    @41
    dvfsumlem1.5
    adantr
    #
    @42
    cY
    @43
    c1
    caddc
    co
    #
    @43
    cfl
    cfv
    #
    c1
    caddc
    co
    cle
    @42
    @65
    cY
    @107
    cle
    wbr
    @66
    cY
    fllep1
    syl
    @42
    @108
    @43
    c1
    caddc
    @42
    @65
    @108
    @43
    wceq
    @66
    cY
    flidm
    syl
    oveq1d
    breqtrrd
    dvfsumlem2
    #
    simpld
    @42
    @44
    @9
    cH
    cfv
    #
    @1
    @86
    @42
    cS
    cr
    @9
    cH
    @59
    wph
    @9
    cS
    wcel
    #
    @41
    wph
    @9
    @10
    cS
    wph
    @9
    @10
    wcel
    #
    @15
    @72
    @19
    @80
    wph
    @76
    @112
    @15
    @72
    wa
    wb
    @77
    cT
    @9
    elioopnf
    syl
    mpbir2and
    dvfsum.s
    syl6eleqr
    adantr
    #
    ffvelrnd
    #
    @88
    @42
    vm
    cH
    @9
    @43
    @42
    @82
    @43
    cz
    wcel
    @81
    @43
    @9
    cuz
    cfv
    wcel
    @83
    @42
    cY
    @66
    flcld
    @84
    @9
    @43
    eluz2
    syl3anbrc
    #
    @42
    vm
    cv
    #
    @9
    @43
    cfz
    co
    wcel
    #
    wa
    #
    cS
    cr
    @116
    cH
    @42
    @45
    @117
    @59
    adantr
    @118
    @116
    @10
    cS
    @118
    @116
    @10
    wcel
    #
    @116
    cr
    wcel
    #
    cT
    @116
    clt
    wbr
    #
    @118
    @116
    @117
    @116
    cz
    wcel
    #
    @42
    @116
    @9
    @43
    elfzelz
    adantl
    zred
    #
    @118
    cT
    @9
    @116
    @42
    @24
    @117
    @69
    adantr
    @42
    @15
    @117
    @71
    adantr
    @123
    wph
    @72
    @41
    @117
    @80
    ad2antrr
    @117
    @9
    @116
    cle
    wbr
    #
    @42
    @116
    @9
    @43
    elfzle1
    adantl
    ltletrd
    @118
    @76
    @119
    @120
    @121
    wa
    wb
    #
    wph
    @76
    @41
    @117
    @77
    ad2antrr
    cT
    @116
    elioopnf
    #
    syl
    mpbir2and
    dvfsum.s
    syl6eleqr
    #
    ffvelrnd
    #
    @42
    @116
    @9
    @43
    c1
    cmin
    co
    #
    cfz
    co
    wcel
    #
    wa
    #
    @116
    c1
    caddc
    co
    #
    cH
    cfv
    #
    @116
    cH
    cfv
    #
    cle
    wbr
    #
    @134
    vx
    @116
    cB
    csb
    #
    cmin
    co
    #
    @133
    vx
    @132
    cB
    csb
    #
    cmin
    co
    #
    cle
    wbr
    #
    @131
    vx
    cA
    cB
    cC
    cD
    cS
    cT
    cU
    vk
    cH
    cM
    cV
    @116
    @132
    cZ
    dvfsum.s
    dvfsum.z
    @42
    @21
    @130
    @93
    adantr
    @42
    @22
    @130
    @94
    adantr
    #
    wph
    @23
    @41
    @130
    dvfsum.md
    ad2antrr
    @42
    @24
    @130
    @69
    adantr
    #
    @42
    @26
    @27
    @130
    @96
    adantlr
    @42
    @26
    @28
    @130
    @97
    adantlr
    @42
    @29
    @30
    @130
    @98
    adantlr
    @42
    @31
    @130
    @99
    adantr
    dvfsum.c
    @42
    @32
    @130
    @100
    adantr
    #
    @42
    @34
    @35
    @36
    @130
    @101
    3adant1r
    dvfsum.h
    @131
    @116
    @10
    cS
    @131
    @119
    @120
    @121
    @131
    @116
    @130
    @122
    @42
    @116
    @9
    @129
    elfzelz
    adantl
    #
    zred
    #
    @131
    cT
    @9
    @116
    @142
    @42
    @15
    @130
    @71
    adantr
    #
    @145
    wph
    @72
    @41
    @130
    @80
    ad2antrr
    @130
    @124
    @42
    @116
    @9
    @129
    elfzle1
    adantl
    #
    ltletrd
    #
    @131
    @76
    @125
    @131
    cT
    @142
    rexrd
    #
    @126
    syl
    mpbir2and
    dvfsum.s
    syl6eleqr
    @131
    @132
    @10
    cS
    @131
    @132
    @10
    wcel
    #
    @132
    cr
    wcel
    #
    cT
    @132
    clt
    wbr
    #
    @131
    @120
    @151
    @145
    @116
    peano2re
    syl
    #
    @131
    cT
    @116
    @132
    @142
    @145
    @153
    @148
    @131
    @116
    @145
    lep1d
    #
    ltletrd
    @131
    @76
    @150
    @151
    @152
    wa
    wb
    @149
    cT
    @132
    elioopnf
    syl
    mpbir2and
    dvfsum.s
    syl6eleqr
    @131
    cD
    @9
    @116
    @141
    @146
    @145
    @42
    cD
    @9
    cle
    wbr
    @130
    @104
    adantr
    @147
    letrd
    @154
    @131
    @132
    @43
    cU
    @131
    @132
    @153
    rexrd
    @42
    @43
    cxr
    wcel
    @130
    @42
    @43
    @68
    rexrd
    #
    adantr
    @143
    @131
    @132
    @43
    cle
    wbr
    #
    @116
    @129
    cle
    wbr
    #
    @130
    @157
    @42
    @116
    @9
    @129
    elfzle2
    adantl
    @131
    @120
    c1
    cr
    wcel
    @63
    @156
    @157
    wb
    @145
    @131
    1red
    @131
    @65
    @63
    @42
    @65
    @130
    @66
    adantr
    @67
    syl
    @116
    c1
    @43
    leaddsub
    syl3anc
    mpbird
    @42
    @43
    cU
    cle
    wbr
    @130
    @42
    @43
    cY
    cU
    @155
    @42
    cY
    @66
    rexrd
    @100
    @105
    @106
    xrletrd
    #
    adantr
    xrletrd
    @131
    @151
    @132
    @116
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    wceq
    @132
    @160
    cle
    wbr
    @153
    @131
    @116
    @159
    c1
    caddc
    @131
    @159
    @116
    @131
    @122
    @159
    @116
    wceq
    @144
    @116
    flid
    syl
    eqcomd
    oveq1d
    @132
    @160
    eqle
    syl2anc
    dvfsumlem2
    #
    simpld
    monoord2
    @42
    @110
    @1
    cle
    wbr
    #
    @4
    @110
    vx
    @9
    cB
    csb
    #
    cmin
    co
    #
    cle
    wbr
    #
    @42
    vx
    cA
    cB
    cC
    cD
    cS
    cT
    cU
    vk
    cH
    cM
    cV
    cX
    @9
    cZ
    dvfsum.s
    dvfsum.z
    @93
    @94
    @95
    @69
    @96
    @97
    @98
    @99
    dvfsum.c
    @100
    @101
    dvfsum.h
    @87
    @113
    @102
    @103
    @42
    @9
    @43
    cU
    @42
    @9
    @71
    rexrd
    @155
    @100
    @84
    @158
    xrletrd
    @42
    @9
    @71
    leidd
    dvfsumlem2
    #
    simpld
    letrd
    letrd
    @42
    @4
    @91
    @6
    @42
    @1
    @3
    @88
    @42
    @37
    @136
    cr
    wcel
    #
    vm
    cS
    wral
    #
    @3
    cr
    wcel
    #
    @87
    @42
    @167
    vm
    cS
    @42
    @30
    vx
    cS
    wral
    #
    @116
    cS
    wcel
    #
    @167
    wph
    @170
    @41
    wph
    @30
    vx
    cS
    @55
    ralrimiva
    adantr
    @30
    @167
    vx
    @116
    cS
    vx
    @136
    cr
    vx
    @116
    cB
    nfcsb1v
    nfel1
    vx
    vm
    weq
    cB
    @136
    cr
    vx
    @116
    cB
    csbeq1a
    eleq1d
    rspc
    mpan9
    #
    ralrimiva
    #
    @167
    @169
    vm
    cX
    cS
    @116
    cX
    wceq
    @136
    @3
    cr
    vx
    @116
    cX
    cB
    csbeq1
    eleq1d
    rspcv
    sylc
    resubcld
    #
    @42
    @44
    @90
    @86
    @42
    @43
    cS
    wcel
    @168
    @90
    cr
    wcel
    #
    @85
    @173
    @167
    @175
    vm
    @43
    cS
    @116
    @43
    wceq
    @136
    @90
    cr
    vx
    @116
    @43
    cB
    csbeq1
    eleq1d
    rspcv
    sylc
    resubcld
    #
    @42
    @0
    @5
    @61
    @42
    @38
    @168
    @5
    cr
    wcel
    #
    @60
    @173
    @167
    @177
    vm
    cY
    cS
    @116
    cY
    wceq
    @136
    @5
    cr
    vx
    @116
    cY
    cB
    csbeq1
    eleq1d
    rspcv
    sylc
    resubcld
    @42
    @4
    @164
    @91
    @174
    @42
    @110
    @163
    @114
    @42
    @111
    @168
    @163
    cr
    wcel
    #
    @113
    @173
    @167
    @178
    vm
    @9
    cS
    @116
    @9
    wceq
    @136
    @163
    cr
    vx
    @116
    @9
    cB
    csbeq1
    eleq1d
    rspcv
    sylc
    resubcld
    @176
    @42
    @162
    @165
    @166
    simprd
    @42
    @9
    vy
    cvv
    vy
    cv
    #
    cH
    cfv
    #
    vx
    @179
    cB
    csb
    #
    cmin
    co
    #
    cmpt
    #
    cfv
    #
    @43
    @183
    cfv
    #
    @164
    @91
    cle
    @42
    vm
    @183
    @9
    @43
    @115
    @118
    @116
    @183
    cfv
    #
    @137
    cr
    @116
    cvv
    wcel
    @186
    @137
    wceq
    vm
    vex
    vy
    @116
    @182
    @137
    cvv
    @183
    vy
    vm
    weq
    @180
    @134
    @181
    @136
    cmin
    @179
    @116
    cH
    fveq2
    vx
    @179
    @116
    cB
    csbeq1
    oveq12d
    @183
    eqid
    #
    @180
    @181
    cmin
    ovex
    #
    fvmpt3i
    ax-mp
    #
    @118
    @134
    @136
    @128
    @42
    @117
    @171
    @167
    @127
    @172
    syldan
    resubcld
    syl5eqel
    @131
    @137
    @139
    @186
    @132
    @183
    cfv
    #
    cle
    @131
    @135
    @140
    @161
    simprd
    @189
    @132
    cvv
    wcel
    @190
    @139
    wceq
    @116
    c1
    caddc
    ovex
    vy
    @132
    @182
    @139
    cvv
    @183
    @179
    @132
    wceq
    @180
    @133
    @181
    @138
    cmin
    @179
    @132
    cH
    fveq2
    vx
    @179
    @132
    cB
    csbeq1
    oveq12d
    @187
    @188
    fvmpt3i
    ax-mp
    3brtr4g
    monoord
    @9
    cvv
    wcel
    @184
    @164
    wceq
    @8
    c1
    caddc
    ovex
    vy
    @9
    @182
    @164
    cvv
    @183
    @179
    @9
    wceq
    @180
    @110
    @181
    @163
    cmin
    @179
    @9
    cH
    fveq2
    vx
    @179
    @9
    cB
    csbeq1
    oveq12d
    @187
    @188
    fvmpt3i
    ax-mp
    @43
    cvv
    wcel
    @185
    @91
    wceq
    cY
    cfl
    fvex
    vy
    @43
    @182
    @91
    cvv
    @183
    @179
    @43
    wceq
    @180
    @44
    @181
    @90
    cmin
    @179
    @43
    cH
    fveq2
    vx
    @179
    @43
    cB
    csbeq1
    oveq12d
    @187
    @188
    fvmpt3i
    ax-mp
    3brtr3g
    letrd
    @42
    @89
    @92
    @109
    simprd
    letrd
    jca
    lecasei
end
