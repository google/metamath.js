include "cfl.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "csb.mm"
include "cmul.mm"
include "cfz.mm"
include "csu.mm"
include "caddc.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wceq.mm"
include "wa.mm"
include "cr.mm"
include "wcel.mm"
include "cz.mm"
include "cle.mm"
include "wb.mm"
include "cpnf.mm"
include "cioo.mm"
include "ioossre.mm"
include "eqsstri.mm"
include "sseldi.mm"
include "flcld.mm"
include "reflcl.mm"
include "syl.mm"
include "flle.mm"
include "letrd.mm"
include "flbi.mm"
include "baibd.mm"
include "syl21anc.mm"
include "biimpar.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "sumeq1d.mm"
include "oveq12d.mm"
include "simpr.mm"
include "adantr.mm"
include "peano2zd.mm"
include "eqeltrd.mm"
include "flid.mm"
include "eqtrd.mm"
include "recnd.mm"
include "subcld.mm"
include "1cnd.mm"
include "cc.mm"
include "wral.mm"
include "cv.mm"
include "wss.mm"
include "a1i.mm"
include "dvmptrecl.mm"
include "ralrimiva.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "rspc.mm"
include "sylc.mm"
include "subdird.mm"
include "subsub4d.mm"
include "mulid2d.mm"
include "3eqtr3d.mm"
include "cuz.mm"
include "zred.mm"
include "peano2rem.mm"
include "1red.mm"
include "lesubaddd.mm"
include "mpbird.mm"
include "peano2zm.mm"
include "flge.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "elfzuz.mm"
include "syl6eleqr.mm"
include "rspccva.mm"
include "syl2an.mm"
include "cvv.mm"
include "eqvisset.mm"
include "eqeq2.mm"
include "csbied.mm"
include "eqcomd.mm"
include "fsumm1.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "csbeq1d.mm"
include "3eqtr4d.mm"
include "fzfid.mm"
include "fsumcl.mm"
include "addsubd.mm"
include "mulcld.mm"
include "nppcan3d.mm"
include "wo.mm"
include "peano2re.mm"
include "leloed.mm"
include "mpjaodan.mm"
include "ovex.mm"
include "nfcv.mm"
include "nfov.mm"
include "id.mm"
include "fveq2.mm"
include "fvmptf.mm"
include "subadd23d.mm"

theorem dvfsumlem1
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
  assume dvfsumlem1.6: |- ( ph -> Y <_ ( ( |_ ` X ) + 1 ) )

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
  assert |- ( ph -> ( H ` Y ) = ( ( ( ( Y - ( |_ ` X ) ) x. [_ Y / x ]_ B ) - [_ Y / x ]_ A ) + sum_ k e. ( M ... ( |_ ` X ) ) C ) )

  proof
    wph
    cY
    cY
    cfl
    cfv
    #
    cmin
    co
    #
    vx
    cY
    cB
    csb
    #
    cmul
    co
    #
    cM
    @0
    cfz
    co
    #
    cC
    vk
    csu
    #
    vx
    cY
    cA
    csb
    #
    cmin
    co
    #
    caddc
    co
    #
    cY
    cX
    cfl
    cfv
    #
    cmin
    co
    #
    @2
    cmul
    co
    #
    cM
    @9
    cfz
    co
    #
    cC
    vk
    csu
    #
    @6
    cmin
    co
    #
    caddc
    co
    #
    cY
    cH
    cfv
    #
    @11
    @6
    cmin
    co
    @13
    caddc
    co
    wph
    cY
    @9
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @8
    @15
    wceq
    cY
    @17
    wceq
    #
    wph
    @18
    wa
    #
    @3
    @11
    @7
    @14
    caddc
    @20
    @1
    @10
    @2
    cmul
    @20
    @0
    @9
    cY
    cmin
    wph
    @0
    @9
    wceq
    #
    @18
    wph
    cY
    cr
    wcel
    #
    @9
    cz
    wcel
    #
    @9
    cY
    cle
    wbr
    #
    @21
    @18
    wb
    wph
    cS
    cr
    cY
    cS
    cT
    cpnf
    cioo
    co
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
    wph
    cS
    cr
    cX
    @25
    dvfsumlem1.1
    sseldi
    #
    flcld
    #
    wph
    @9
    cX
    cY
    wph
    cX
    cr
    wcel
    #
    @9
    cr
    wcel
    #
    @27
    cX
    reflcl
    syl
    #
    @27
    @26
    wph
    @29
    @9
    cX
    cle
    wbr
    @27
    cX
    flle
    syl
    dvfsumlem1.4
    letrd
    @22
    @23
    wa
    @21
    @24
    @18
    cY
    @9
    flbi
    baibd
    syl21anc
    biimpar
    #
    oveq2d
    oveq1d
    @20
    @5
    @13
    @6
    cmin
    @20
    @4
    @12
    cC
    vk
    @20
    @0
    @9
    cM
    cfz
    @32
    oveq2d
    sumeq1d
    oveq1d
    oveq12d
    wph
    @19
    wa
    #
    @8
    @11
    @2
    cmin
    co
    #
    @14
    @2
    caddc
    co
    #
    caddc
    co
    @15
    @33
    @3
    @34
    @7
    @35
    caddc
    @33
    @3
    cY
    @17
    cmin
    co
    #
    @2
    cmul
    co
    #
    @34
    @33
    @1
    @36
    @2
    cmul
    @33
    @0
    @17
    cY
    cmin
    @33
    @0
    cY
    @17
    @33
    cY
    cz
    wcel
    @0
    cY
    wceq
    @33
    cY
    @17
    cz
    wph
    @19
    simpr
    #
    @33
    @9
    @33
    cX
    wph
    @29
    @19
    @27
    adantr
    flcld
    peano2zd
    eqeltrd
    cY
    flid
    syl
    @38
    eqtrd
    #
    oveq2d
    oveq1d
    wph
    @37
    @34
    wceq
    @19
    wph
    @10
    c1
    cmin
    co
    #
    @2
    cmul
    co
    @11
    c1
    @2
    cmul
    co
    #
    cmin
    co
    @37
    @34
    wph
    @10
    c1
    @2
    wph
    cY
    @9
    wph
    cY
    @26
    recnd
    #
    wph
    @9
    @31
    recnd
    #
    subcld
    #
    wph
    1cnd
    #
    wph
    cY
    cS
    wcel
    #
    cB
    cc
    wcel
    #
    vx
    cS
    wral
    @2
    cc
    wcel
    #
    dvfsumlem1.2
    wph
    @47
    vx
    cS
    wph
    vx
    cv
    #
    cS
    wcel
    wa
    #
    cB
    wph
    vx
    cA
    cB
    cS
    cV
    cS
    cr
    wss
    wph
    @25
    a1i
    dvfsum.a
    dvfsum.b1
    dvfsum.b3
    dvmptrecl
    recnd
    ralrimiva
    @47
    @48
    vx
    cY
    cS
    vx
    @2
    cc
    vx
    cY
    cB
    nfcsb1v
    #
    nfel1
    @49
    cY
    wceq
    #
    cB
    @2
    cc
    vx
    cY
    cB
    csbeq1a
    #
    eleq1d
    rspc
    sylc
    #
    subdird
    wph
    @40
    @36
    @2
    cmul
    wph
    cY
    @9
    c1
    @42
    @43
    @45
    subsub4d
    oveq1d
    wph
    @41
    @2
    @11
    cmin
    wph
    @2
    @54
    mulid2d
    oveq2d
    3eqtr3d
    adantr
    eqtrd
    @33
    @7
    @13
    @2
    caddc
    co
    #
    @6
    cmin
    co
    #
    @35
    @33
    @5
    @55
    @6
    cmin
    @33
    cM
    @17
    cfz
    co
    #
    cC
    vk
    csu
    #
    @13
    vx
    @17
    cB
    csb
    #
    caddc
    co
    #
    @5
    @55
    wph
    @58
    @60
    wceq
    @19
    wph
    @58
    cM
    @17
    c1
    cmin
    co
    #
    cfz
    co
    #
    cC
    vk
    csu
    #
    @59
    caddc
    co
    @60
    wph
    cC
    @59
    vk
    cM
    @17
    wph
    cM
    cz
    wcel
    #
    @17
    cz
    wcel
    cM
    @17
    cle
    wbr
    #
    @17
    cM
    cuz
    cfv
    #
    wcel
    dvfsum.m
    wph
    @9
    @28
    peano2zd
    wph
    cM
    c1
    cmin
    co
    #
    @9
    cle
    wbr
    #
    @65
    wph
    @67
    cX
    cle
    wbr
    #
    @68
    wph
    @67
    cD
    cX
    wph
    cM
    cr
    wcel
    @67
    cr
    wcel
    wph
    cM
    dvfsum.m
    zred
    #
    cM
    peano2rem
    syl
    dvfsum.d
    @27
    wph
    @67
    cD
    cle
    wbr
    cM
    cD
    c1
    caddc
    co
    cle
    wbr
    dvfsum.md
    wph
    cM
    c1
    cD
    @70
    wph
    1red
    #
    dvfsum.d
    lesubaddd
    mpbird
    dvfsumlem1.3
    letrd
    wph
    @29
    @67
    cz
    wcel
    #
    @69
    @68
    wb
    @27
    wph
    @64
    @72
    dvfsum.m
    cM
    peano2zm
    syl
    cX
    @67
    flge
    syl2anc
    mpbid
    wph
    cM
    c1
    @9
    @70
    @71
    @31
    lesubaddd
    mpbid
    cM
    @17
    eluz2
    syl3anbrc
    wph
    @47
    vx
    cZ
    wral
    #
    vk
    cv
    #
    cZ
    wcel
    #
    cC
    cc
    wcel
    #
    @74
    @57
    wcel
    #
    wph
    @47
    vx
    cZ
    wph
    @49
    cZ
    wcel
    wa
    cB
    dvfsum.b2
    recnd
    ralrimiva
    #
    @77
    @74
    @66
    cZ
    @74
    cM
    @17
    elfzuz
    dvfsum.z
    syl6eleqr
    @47
    @76
    vx
    @74
    cZ
    @49
    @74
    wceq
    #
    cB
    cC
    cc
    dvfsum.c
    eleq1d
    rspccva
    #
    syl2an
    @74
    @17
    wceq
    #
    @59
    cC
    @81
    vx
    @17
    cB
    cC
    cvv
    vk
    @17
    eqvisset
    @81
    @49
    @17
    wceq
    #
    wa
    @79
    cB
    cC
    wceq
    @81
    @79
    @82
    @74
    @17
    @49
    eqeq2
    biimpar
    dvfsum.c
    syl
    csbied
    eqcomd
    fsumm1
    wph
    @63
    @13
    @59
    caddc
    wph
    @62
    @12
    cC
    vk
    wph
    @61
    @9
    cM
    cfz
    wph
    @9
    cc
    wcel
    c1
    cc
    wcel
    @61
    @9
    wceq
    @43
    ax-1cn
    @9
    c1
    pncan
    sylancl
    oveq2d
    sumeq1d
    oveq1d
    eqtrd
    adantr
    @33
    @4
    @57
    cC
    vk
    @33
    @0
    @17
    cM
    cfz
    @39
    oveq2d
    sumeq1d
    @33
    @2
    @59
    @13
    caddc
    @33
    vx
    cY
    @17
    cB
    @38
    csbeq1d
    oveq2d
    3eqtr4d
    oveq1d
    wph
    @56
    @35
    wceq
    @19
    wph
    @13
    @2
    @6
    wph
    @12
    cC
    vk
    wph
    cM
    @9
    fzfid
    wph
    @73
    @75
    @76
    @74
    @12
    wcel
    #
    @78
    @83
    @74
    @66
    cZ
    @74
    cM
    @9
    elfzuz
    dvfsum.z
    syl6eleqr
    @80
    syl2an
    fsumcl
    #
    @54
    wph
    @46
    cA
    cc
    wcel
    #
    vx
    cS
    wral
    @6
    cc
    wcel
    #
    dvfsumlem1.2
    wph
    @85
    vx
    cS
    @50
    cA
    dvfsum.a
    recnd
    ralrimiva
    @85
    @86
    vx
    cY
    cS
    vx
    @6
    cc
    vx
    cY
    cA
    nfcsb1v
    #
    nfel1
    @52
    cA
    @6
    cc
    vx
    cY
    cA
    csbeq1a
    #
    eleq1d
    rspc
    sylc
    #
    addsubd
    adantr
    eqtrd
    oveq12d
    @33
    @11
    @2
    @14
    wph
    @11
    cc
    wcel
    @19
    wph
    @10
    @2
    @44
    @54
    mulcld
    #
    adantr
    wph
    @48
    @19
    @54
    adantr
    wph
    @14
    cc
    wcel
    @19
    wph
    @13
    @6
    @84
    @89
    subcld
    adantr
    nppcan3d
    eqtrd
    wph
    cY
    @17
    cle
    wbr
    @18
    @19
    wo
    dvfsumlem1.6
    wph
    cY
    @17
    @26
    wph
    @30
    @17
    cr
    wcel
    @31
    @9
    peano2re
    syl
    leloed
    mpbid
    mpjaodan
    wph
    @46
    @8
    cvv
    wcel
    @16
    @8
    wceq
    dvfsumlem1.2
    @3
    @7
    caddc
    ovex
    vx
    cY
    @49
    @49
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
    @91
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
    @8
    cS
    cH
    cvv
    vx
    cY
    nfcv
    vx
    @3
    @7
    caddc
    vx
    @1
    @2
    cmul
    vx
    @1
    nfcv
    vx
    cmul
    nfcv
    @51
    nfov
    vx
    caddc
    nfcv
    vx
    @5
    @6
    cmin
    vx
    @5
    nfcv
    vx
    cmin
    nfcv
    @87
    nfov
    nfov
    @52
    @93
    @3
    @96
    @7
    caddc
    @52
    @92
    @1
    cB
    @2
    cmul
    @52
    @49
    cY
    @91
    @0
    cmin
    @52
    id
    @49
    cY
    cfl
    fveq2
    #
    oveq12d
    @53
    oveq12d
    @52
    @95
    @5
    cA
    @6
    cmin
    @52
    @94
    @4
    cC
    vk
    @52
    @91
    @0
    cM
    cfz
    @97
    oveq2d
    sumeq1d
    @88
    oveq12d
    oveq12d
    dvfsum.h
    fvmptf
    sylancl
    wph
    @11
    @6
    @13
    @90
    @89
    @84
    subadd23d
    3eqtr4d
end
