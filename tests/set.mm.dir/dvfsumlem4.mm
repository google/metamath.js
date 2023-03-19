include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfl.mm"
include "cfz.mm"
include "csu.mm"
include "csb.mm"
include "cle.mm"
include "wcel.mm"
include "cr.mm"
include "wceq.mm"
include "fzfid.mm"
include "wral.mm"
include "cv.mm"
include "ralrimiva.mm"
include "cuz.mm"
include "elfzuz.mm"
include "syl6eleqr.mm"
include "weq.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "syl2an.mm"
include "fsumrecl.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "csbeq1a.mm"
include "rspc.mm"
include "sylc.mm"
include "resubcld.mm"
include "nfcv.mm"
include "nfov.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "sumeq1d.mm"
include "oveq12d.mm"
include "fvmptf.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "wbr.mm"
include "caddc.mm"
include "cmul.mm"
include "wss.mm"
include "cpnf.mm"
include "cioo.mm"
include "ioossre.mm"
include "eqsstri.mm"
include "a1i.mm"
include "dvmptrecl.mm"
include "nfv.mm"
include "cbvral.mm"
include "sylib.mm"
include "csbeq1.mm"
include "rspcv.mm"
include "sseldi.mm"
include "reflcl.mm"
include "syl.mm"
include "remulcld.mm"
include "readdcld.mm"
include "cc0.mm"
include "fracge0.mm"
include "w3a.mm"
include "rexrd.mm"
include "xrletrd.mm"
include "3jca.mm"
include "wa.mm"
include "simpr1.mm"
include "wi.mm"
include "nfbr.mm"
include "nfim.mm"
include "eleq1.mm"
include "breq2.mm"
include "breq1.mm"
include "3anbi123d.mm"
include "anbi2d.mm"
include "breq2d.mm"
include "imbi12d.mm"
include "vtoclg1f.mm"
include "mpcom.mm"
include "mpdan.mm"
include "mulge0d.mm"
include "addge02d.mm"
include "mpbid.mm"
include "lesub1dd.mm"
include "cmpt.mm"
include "eqid.mm"
include "dvfsumlem3.mm"
include "simprd.mm"
include "id.mm"
include "oveq1d.mm"
include "3brtr3d.mm"
include "recnd.mm"
include "subsub3d.mm"
include "addcomd.mm"
include "eqtrd.mm"
include "c1.mm"
include "1red.mm"
include "letrd.mm"
include "fracle1.mm"
include "lemul1ad.mm"
include "mulid2d.mm"
include "breqtrd.mm"
include "subge0d.mm"
include "mpbird.mm"
include "subge02d.mm"
include "eqbrtrrd.mm"
include "simpld.mm"
include "leadd1dd.mm"
include "absdifled.mm"
include "mpbir2and.mm"
include "eqbrtrd.mm"

theorem dvfsumlem4
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
  let cG: class G
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
  let cH: class H
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
  assume dvfsumlem4.g: |- G = ( x e. S |-> ( sum_ k e. ( M ... ( |_ ` x ) ) C - A ) )
  assume dvfsumlem4.0: |- ( ( ph /\ ( x e. S /\ D <_ x /\ x <_ U ) ) -> 0 <_ B )
  assume dvfsumlem4.1: |- ( ph -> X e. S )
  assume dvfsumlem4.2: |- ( ph -> Y e. S )
  assume dvfsumlem4.3: |- ( ph -> D <_ X )
  assume dvfsumlem4.4: |- ( ph -> X <_ Y )
  assume dvfsumlem4.5: |- ( ph -> Y <_ U )

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
  assert |- ( ph -> ( abs ` ( ( G ` Y ) - ( G ` X ) ) ) <_ [_ X / x ]_ B )

  proof
    wph
    cY
    cG
    cfv
    #
    cX
    cG
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    cM
    cY
    cfl
    cfv
    #
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
    cM
    cX
    cfl
    cfv
    #
    cfz
    co
    #
    cC
    vk
    csu
    #
    vx
    cX
    cA
    csb
    #
    cmin
    co
    #
    cmin
    co
    #
    cabs
    cfv
    #
    vx
    cX
    cB
    csb
    #
    cle
    wph
    @2
    @13
    cabs
    wph
    @0
    @7
    @1
    @12
    cmin
    wph
    cY
    cS
    wcel
    #
    @7
    cr
    wcel
    @0
    @7
    wceq
    dvfsumlem4.2
    wph
    @5
    @6
    wph
    @4
    cC
    vk
    wph
    cM
    @3
    fzfid
    wph
    cB
    cr
    wcel
    #
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
    cr
    wcel
    #
    @19
    @4
    wcel
    #
    wph
    @17
    vx
    cZ
    dvfsum.b2
    ralrimiva
    #
    @22
    @19
    cM
    cuz
    cfv
    #
    cZ
    @19
    cM
    @3
    elfzuz
    dvfsum.z
    syl6eleqr
    @17
    @21
    vx
    @19
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
    #
    syl2an
    fsumrecl
    wph
    @16
    cA
    cr
    wcel
    #
    vx
    cS
    wral
    #
    @6
    cr
    wcel
    #
    dvfsumlem4.2
    wph
    @26
    vx
    cS
    dvfsum.a
    ralrimiva
    #
    @26
    @28
    vx
    cY
    cS
    vx
    @6
    cr
    vx
    cY
    cA
    nfcsb1v
    #
    nfel1
    vx
    cv
    #
    cY
    wceq
    #
    cA
    @6
    cr
    vx
    cY
    cA
    csbeq1a
    #
    eleq1d
    rspc
    sylc
    resubcld
    #
    vx
    cY
    cM
    @31
    cfl
    cfv
    #
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
    @7
    cS
    cG
    cr
    vx
    cY
    nfcv
    #
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
    #
    @30
    nfov
    #
    @32
    @37
    @5
    cA
    @6
    cmin
    @32
    @36
    @4
    cC
    vk
    @32
    @35
    @3
    cM
    cfz
    @31
    cY
    cfl
    fveq2
    #
    oveq2d
    sumeq1d
    @33
    oveq12d
    #
    dvfsumlem4.g
    fvmptf
    syl2anc
    wph
    cX
    cS
    wcel
    #
    @12
    cr
    wcel
    @1
    @12
    wceq
    dvfsumlem4.1
    wph
    @10
    @11
    wph
    @9
    cC
    vk
    wph
    cM
    @8
    fzfid
    wph
    @18
    @20
    @21
    @19
    @9
    wcel
    #
    @23
    @45
    @19
    @24
    cZ
    @19
    cM
    @8
    elfzuz
    dvfsum.z
    syl6eleqr
    @25
    syl2an
    fsumrecl
    wph
    @44
    @27
    @11
    cr
    wcel
    #
    dvfsumlem4.1
    @29
    @26
    @46
    vx
    cX
    cS
    vx
    @11
    cr
    vx
    cX
    cA
    nfcsb1v
    #
    nfel1
    @31
    cX
    wceq
    #
    cA
    @11
    cr
    vx
    cX
    cA
    csbeq1a
    #
    eleq1d
    rspc
    sylc
    resubcld
    #
    vx
    cX
    @38
    @12
    cS
    cG
    cr
    vx
    cX
    nfcv
    #
    vx
    @10
    @11
    cmin
    vx
    @10
    nfcv
    @40
    @47
    nfov
    #
    @48
    @37
    @10
    cA
    @11
    cmin
    @48
    @36
    @9
    cC
    vk
    @48
    @35
    @8
    cM
    cfz
    @31
    cX
    cfl
    fveq2
    #
    oveq2d
    sumeq1d
    @49
    oveq12d
    #
    dvfsumlem4.g
    fvmptf
    syl2anc
    oveq12d
    fveq2d
    wph
    @14
    @15
    cle
    wbr
    @12
    @15
    cmin
    co
    #
    @7
    cle
    wbr
    @7
    @12
    @15
    caddc
    co
    #
    cle
    wbr
    wph
    @55
    cX
    @8
    cmin
    co
    #
    @15
    cmul
    co
    #
    @12
    caddc
    co
    #
    @15
    cmin
    co
    #
    @7
    wph
    @12
    @15
    @50
    wph
    @44
    vx
    vm
    cv
    #
    cB
    csb
    #
    cr
    wcel
    #
    vm
    cS
    wral
    #
    @15
    cr
    wcel
    #
    dvfsumlem4.1
    wph
    @17
    vx
    cS
    wral
    @64
    wph
    @17
    vx
    cS
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
    a1i
    dvfsum.a
    dvfsum.b1
    dvfsum.b3
    dvmptrecl
    ralrimiva
    @17
    @63
    vx
    vm
    cS
    @17
    vm
    nfv
    vx
    @62
    cr
    vx
    @61
    cB
    nfcsb1v
    nfel1
    vx
    vm
    weq
    cB
    @62
    cr
    vx
    @61
    cB
    csbeq1a
    eleq1d
    cbvral
    sylib
    #
    @63
    @65
    vm
    cX
    cS
    @61
    cX
    wceq
    @62
    @15
    cr
    vx
    @61
    cX
    cB
    csbeq1
    eleq1d
    rspcv
    sylc
    #
    resubcld
    wph
    @59
    @15
    wph
    @58
    @12
    wph
    @57
    @15
    wph
    cX
    @8
    wph
    cS
    cr
    cX
    @66
    dvfsumlem4.1
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
    @69
    cX
    reflcl
    syl
    resubcld
    #
    @68
    remulcld
    #
    @50
    readdcld
    #
    @68
    resubcld
    #
    @34
    wph
    @12
    @59
    @15
    @50
    @73
    @68
    wph
    cc0
    @58
    cle
    wbr
    @12
    @59
    cle
    wbr
    wph
    @57
    @15
    @71
    @68
    wph
    @70
    cc0
    @57
    cle
    wbr
    @69
    cX
    fracge0
    syl
    wph
    @44
    cD
    cX
    cle
    wbr
    #
    cX
    cU
    cle
    wbr
    #
    w3a
    #
    cc0
    @15
    cle
    wbr
    #
    wph
    @44
    @75
    @76
    dvfsumlem4.1
    dvfsumlem4.3
    wph
    cX
    cY
    cU
    wph
    cX
    @69
    rexrd
    wph
    cY
    wph
    cS
    cr
    cY
    @66
    dvfsumlem4.2
    sseldi
    #
    rexrd
    dvfsum.u
    dvfsumlem4.4
    dvfsumlem4.5
    xrletrd
    3jca
    @44
    wph
    @77
    wa
    #
    @78
    wph
    @44
    @75
    @76
    simpr1
    wph
    @31
    cS
    wcel
    #
    cD
    @31
    cle
    wbr
    #
    @31
    cU
    cle
    wbr
    #
    w3a
    #
    wa
    #
    cc0
    cB
    cle
    wbr
    #
    wi
    #
    @80
    @78
    wi
    vx
    cX
    cS
    @80
    @78
    vx
    @80
    vx
    nfv
    vx
    cc0
    @15
    cle
    vx
    cc0
    nfcv
    #
    vx
    cle
    nfcv
    #
    vx
    cX
    cB
    nfcsb1v
    #
    nfbr
    nfim
    @48
    @85
    @80
    @86
    @78
    @48
    @84
    @77
    wph
    @48
    @81
    @44
    @82
    @75
    @83
    @76
    @31
    cX
    cS
    eleq1
    @31
    cX
    cD
    cle
    breq2
    @31
    cX
    cU
    cle
    breq1
    3anbi123d
    anbi2d
    @48
    cB
    @15
    cc0
    cle
    vx
    cX
    cB
    csbeq1a
    #
    breq2d
    imbi12d
    dvfsumlem4.0
    vtoclg1f
    mpcom
    mpdan
    #
    mulge0d
    wph
    @12
    @58
    @50
    @72
    addge02d
    mpbid
    lesub1dd
    wph
    @60
    cY
    @3
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
    @7
    caddc
    co
    #
    @94
    cmin
    co
    #
    @7
    @74
    wph
    @96
    @94
    wph
    @95
    @7
    wph
    @93
    @94
    wph
    cY
    @3
    @79
    wph
    cY
    cr
    wcel
    #
    @3
    cr
    wcel
    @79
    cY
    reflcl
    syl
    resubcld
    #
    wph
    @16
    @64
    @94
    cr
    wcel
    #
    dvfsumlem4.2
    @67
    @63
    @100
    vm
    cY
    cS
    @61
    cY
    wceq
    @62
    @94
    cr
    vx
    @61
    cY
    cB
    csbeq1
    eleq1d
    rspcv
    sylc
    #
    remulcld
    #
    @34
    readdcld
    #
    @101
    resubcld
    @34
    wph
    cX
    vx
    cS
    @31
    @35
    cmin
    co
    #
    cB
    cmul
    co
    #
    @38
    caddc
    co
    #
    cmpt
    #
    cfv
    #
    @15
    cmin
    co
    #
    cY
    @107
    cfv
    #
    @94
    cmin
    co
    #
    @60
    @97
    cle
    wph
    @110
    @108
    cle
    wbr
    #
    @109
    @111
    cle
    wbr
    #
    wph
    vx
    cA
    cB
    cC
    cD
    cS
    cT
    cU
    vk
    @107
    cM
    cV
    cX
    cY
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
    dvfsum.u
    dvfsum.l
    @107
    eqid
    #
    dvfsumlem4.1
    dvfsumlem4.2
    dvfsumlem4.3
    dvfsumlem4.4
    dvfsumlem4.5
    dvfsumlem3
    #
    simprd
    wph
    @108
    @59
    @15
    cmin
    wph
    @44
    @59
    cr
    wcel
    @108
    @59
    wceq
    dvfsumlem4.1
    @73
    vx
    cX
    @106
    @59
    cS
    @107
    cr
    @51
    vx
    @58
    @12
    caddc
    vx
    @57
    @15
    cmul
    vx
    @57
    nfcv
    vx
    cmul
    nfcv
    #
    @90
    nfov
    vx
    caddc
    nfcv
    #
    @52
    nfov
    @48
    @105
    @58
    @38
    @12
    caddc
    @48
    @104
    @57
    cB
    @15
    cmul
    @48
    @31
    cX
    @35
    @8
    cmin
    @48
    id
    @53
    oveq12d
    @91
    oveq12d
    @54
    oveq12d
    @114
    fvmptf
    syl2anc
    #
    oveq1d
    wph
    @110
    @96
    @94
    cmin
    wph
    @16
    @96
    cr
    wcel
    @110
    @96
    wceq
    dvfsumlem4.2
    @103
    vx
    cY
    @106
    @96
    cS
    @107
    cr
    @39
    vx
    @95
    @7
    caddc
    vx
    @93
    @94
    cmul
    vx
    @93
    nfcv
    @116
    vx
    cY
    cB
    nfcsb1v
    #
    nfov
    @117
    @41
    nfov
    @32
    @105
    @95
    @38
    @7
    caddc
    @32
    @104
    @93
    cB
    @94
    cmul
    @32
    @31
    cY
    @35
    @3
    cmin
    @32
    id
    @42
    oveq12d
    vx
    cY
    cB
    csbeq1a
    #
    oveq12d
    @43
    oveq12d
    @114
    fvmptf
    syl2anc
    #
    oveq1d
    3brtr3d
    wph
    @7
    @94
    @95
    cmin
    co
    #
    cmin
    co
    #
    @97
    @7
    cle
    wph
    @123
    @7
    @95
    caddc
    co
    #
    @94
    cmin
    co
    @97
    wph
    @7
    @94
    @95
    wph
    @7
    @34
    recnd
    #
    wph
    @94
    @101
    recnd
    #
    wph
    @95
    @102
    recnd
    #
    subsub3d
    wph
    @124
    @96
    @94
    cmin
    wph
    @7
    @95
    @125
    @127
    addcomd
    oveq1d
    eqtrd
    wph
    cc0
    @122
    cle
    wbr
    #
    @123
    @7
    cle
    wbr
    wph
    @128
    @95
    @94
    cle
    wbr
    wph
    @95
    c1
    @94
    cmul
    co
    @94
    cle
    wph
    @93
    c1
    @94
    @99
    wph
    1red
    #
    @101
    wph
    @16
    cD
    cY
    cle
    wbr
    #
    cY
    cU
    cle
    wbr
    #
    w3a
    #
    cc0
    @94
    cle
    wbr
    #
    wph
    @16
    @130
    @131
    dvfsumlem4.2
    wph
    cD
    cX
    cY
    dvfsum.d
    @69
    @79
    dvfsumlem4.3
    dvfsumlem4.4
    letrd
    dvfsumlem4.5
    3jca
    @16
    wph
    @132
    wa
    #
    @133
    wph
    @16
    @130
    @131
    simpr1
    @87
    @134
    @133
    wi
    vx
    cY
    cS
    @134
    @133
    vx
    @134
    vx
    nfv
    vx
    cc0
    @94
    cle
    @88
    @89
    @119
    nfbr
    nfim
    @32
    @85
    @134
    @86
    @133
    @32
    @84
    @132
    wph
    @32
    @81
    @16
    @82
    @130
    @83
    @131
    @31
    cY
    cS
    eleq1
    @31
    cY
    cD
    cle
    breq2
    @31
    cY
    cU
    cle
    breq1
    3anbi123d
    anbi2d
    @32
    cB
    @94
    cc0
    cle
    @120
    breq2d
    imbi12d
    dvfsumlem4.0
    vtoclg1f
    mpcom
    mpdan
    #
    wph
    @98
    @93
    c1
    cle
    wbr
    @79
    cY
    fracle1
    syl
    lemul1ad
    wph
    @94
    @126
    mulid2d
    breqtrd
    wph
    @94
    @95
    @101
    @102
    subge0d
    mpbird
    wph
    @7
    @122
    @34
    wph
    @94
    @95
    @101
    @102
    resubcld
    subge02d
    mpbid
    eqbrtrrd
    letrd
    letrd
    wph
    @7
    @15
    @12
    caddc
    co
    #
    @56
    cle
    wph
    @7
    @59
    @136
    @34
    @73
    wph
    @15
    @12
    @68
    @50
    readdcld
    wph
    @7
    @96
    @59
    @34
    @103
    @73
    wph
    cc0
    @95
    cle
    wbr
    @7
    @96
    cle
    wbr
    wph
    @93
    @94
    @99
    @101
    wph
    @98
    cc0
    @93
    cle
    wbr
    @79
    cY
    fracge0
    syl
    @135
    mulge0d
    wph
    @7
    @95
    @34
    @102
    addge02d
    mpbid
    wph
    @110
    @108
    @96
    @59
    cle
    wph
    @112
    @113
    @115
    simpld
    @121
    @118
    3brtr3d
    letrd
    wph
    @58
    @15
    @12
    @72
    @68
    @50
    wph
    @58
    c1
    @15
    cmul
    co
    @15
    cle
    wph
    @57
    c1
    @15
    @71
    @129
    @68
    @92
    wph
    @70
    @57
    c1
    cle
    wbr
    @69
    cX
    fracle1
    syl
    lemul1ad
    wph
    @15
    wph
    @15
    @68
    recnd
    #
    mulid2d
    breqtrd
    leadd1dd
    letrd
    wph
    @15
    @12
    @137
    wph
    @12
    @50
    recnd
    addcomd
    breqtrd
    wph
    @7
    @12
    @15
    @34
    @50
    @68
    absdifled
    mpbir2and
    eqbrtrd
end
