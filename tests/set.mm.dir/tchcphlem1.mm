include "co.mm"
include "csqrt.mm"
include "cfv.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "c2.mm"
include "cexp.mm"
include "cmul.mm"
include "cabs.mm"
include "wcel.mm"
include "cr.mm"
include "cgrp.mm"
include "cphl.mm"
include "clmod.mm"
include "phllmod.mm"
include "lmodgrp.mm"
include "3syl.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "tchcphlem3.mm"
include "mpdan.mm"
include "readdcld.mm"
include "cc.mm"
include "cclm.mm"
include "wss.mm"
include "tchclm.mm"
include "clmsscn.mm"
include "syl.mm"
include "ipcl.mm"
include "sseldd.mm"
include "addcld.mm"
include "abscld.mm"
include "recnd.mm"
include "2re.mm"
include "cc0.mm"
include "cv.mm"
include "wral.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "oveq12.mm"
include "anidms.mm"
include "breq2d.mm"
include "rspcv.mm"
include "sylc.mm"
include "resqrtcld.mm"
include "remulcld.mm"
include "remulcl.mm"
include "sylancr.mm"
include "add32d.mm"
include "eqeltrd.mm"
include "cmin.mm"
include "absidd.mm"
include "csg.mm"
include "cplusg.mm"
include "clmadd.mm"
include "oveqd.mm"
include "oveq12d.mm"
include "clmacl.mm"
include "clmsub.mm"
include "eqid.mm"
include "ip2subdi.mm"
include "3eqtr4rd.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "abs2dif2d.mm"
include "eqbrtrd.mm"
include "addge0d.mm"
include "oveq1d.mm"
include "breqtrd.mm"
include "abstrid.mm"
include "2timesd.mm"
include "ccj.mm"
include "abscjd.mm"
include "cstv.mm"
include "clmcj.mm"
include "fveq1d.mm"
include "ipcj.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "breqtrrd.mm"
include "cnm.mm"
include "cdiv.mm"
include "ipcau2.mm"
include "tchnmval.mm"
include "syl2anc.mm"
include "clt.mm"
include "wb.mm"
include "a1i.mm"
include "2pos.mm"
include "lemul2.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "letrd.mm"
include "leadd2dd.mm"
include "sqsqrtd.mm"
include "sqrtcld.mm"
include "binom2.mm"
include "3brtr4d.mm"
include "sqrtge0d.mm"
include "le2sqd.mm"
include "mpbird.mm"

theorem tchcphlem1
  let wph: wff ph
  let vx: setvar x
  let cF: class F
  let cG: class G
  let c.xi: class .,
  let cK: class K
  let c.mi: class .-
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let c.x: class .x.
  assume tchval.n: |- G = ( toCHil ` W )
  assume tchcph.v: |- V = ( Base ` W )
  assume tchcph.f: |- F = ( Scalar ` W )
  assume tchcph.1: |- ( ph -> W e. PreHil )
  assume tchcph.2: |- ( ph -> F = ( CCfld |`s K ) )
  assume tchcph.h: |- ., = ( .i ` W )
  assume tchcph.3: |- ( ( ph /\ ( x e. K /\ x e. RR /\ 0 <_ x ) ) -> ( sqrt ` x ) e. K )
  assume tchcph.4: |- ( ( ph /\ x e. V ) -> 0 <_ ( x ., x ) )
  assume tchcph.k: |- K = ( Base ` F )
  assume tchcph.m: |- .- = ( -g ` W )
  assume tchcphlem1.3: |- ( ph -> X e. V )
  assume tchcphlem1.4: |- ( ph -> Y e. V )

  disjoint .- x
  disjoint ., x
  disjoint F x
  disjoint G x
  disjoint V x
  disjoint ph x
  disjoint W x
  disjoint X x
  disjoint Y x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint ., w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint ., y
  disjoint ., z
  disjoint F y
  disjoint F z
  disjoint G y
  disjoint G z
  disjoint V w
  disjoint V y
  disjoint V z
  disjoint C x
  disjoint ph y
  disjoint ph z
  disjoint W w
  disjoint W y
  disjoint W z
  disjoint .x. x
  assert |- ( ph -> ( sqrt ` ( ( X .- Y ) ., ( X .- Y ) ) ) <_ ( ( sqrt ` ( X ., X ) ) + ( sqrt ` ( Y ., Y ) ) ) )

  proof
    wph
    cX
    cY
    c.mi
    co
    #
    @0
    c.xi
    co
    #
    csqrt
    cfv
    #
    cX
    cX
    c.xi
    co
    #
    csqrt
    cfv
    #
    cY
    cY
    c.xi
    co
    #
    csqrt
    cfv
    #
    caddc
    co
    #
    cle
    wbr
    @2
    c2
    cexp
    co
    #
    @7
    c2
    cexp
    co
    #
    cle
    wbr
    wph
    @1
    @3
    c2
    @4
    @6
    cmul
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    @5
    caddc
    co
    #
    @8
    @9
    cle
    wph
    @1
    @3
    @5
    caddc
    co
    #
    cX
    cY
    c.xi
    co
    #
    cY
    cX
    c.xi
    co
    #
    caddc
    co
    #
    cabs
    cfv
    #
    caddc
    co
    #
    @13
    wph
    @0
    cV
    wcel
    #
    @1
    cr
    wcel
    wph
    cW
    cgrp
    wcel
    #
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    @20
    wph
    cW
    cphl
    wcel
    #
    cW
    clmod
    wcel
    @21
    tchcph.1
    cW
    phllmod
    cW
    lmodgrp
    3syl
    #
    tchcphlem1.3
    tchcphlem1.4
    cV
    cW
    c.mi
    cX
    cY
    tchcph.v
    tchcph.m
    grpsubcl
    syl3anc
    #
    wph
    cF
    cG
    c.xi
    cK
    cV
    cW
    @0
    tchval.n
    tchcph.v
    tchcph.f
    tchcph.1
    tchcph.2
    tchcph.h
    tchcphlem3
    mpdan
    #
    wph
    @14
    @18
    wph
    @3
    @5
    wph
    @22
    @3
    cr
    wcel
    tchcphlem1.3
    wph
    cF
    cG
    c.xi
    cK
    cV
    cW
    cX
    tchval.n
    tchcph.v
    tchcph.f
    tchcph.1
    tchcph.2
    tchcph.h
    tchcphlem3
    mpdan
    #
    wph
    @23
    @5
    cr
    wcel
    tchcphlem1.4
    wph
    cF
    cG
    c.xi
    cK
    cV
    cW
    cY
    tchval.n
    tchcph.v
    tchcph.f
    tchcph.1
    tchcph.2
    tchcph.h
    tchcphlem3
    mpdan
    #
    readdcld
    #
    wph
    @17
    wph
    @15
    @16
    wph
    cK
    cc
    @15
    wph
    cW
    cclm
    wcel
    #
    cK
    cc
    wss
    wph
    cF
    cG
    cK
    cV
    cW
    tchval.n
    tchcph.v
    tchcph.f
    tchcph.1
    tchcph.2
    tchclm
    #
    cF
    cK
    cW
    tchcph.f
    tchcph.k
    clmsscn
    syl
    #
    wph
    @24
    @22
    @23
    @15
    cK
    wcel
    #
    tchcph.1
    tchcphlem1.3
    tchcphlem1.4
    cX
    cY
    cF
    c.xi
    cK
    cV
    cW
    tchcph.f
    tchcph.h
    tchcph.v
    tchcph.k
    ipcl
    syl3anc
    #
    sseldd
    #
    wph
    cK
    cc
    @16
    @33
    wph
    @24
    @23
    @22
    @16
    cK
    wcel
    #
    tchcph.1
    tchcphlem1.4
    tchcphlem1.3
    cY
    cX
    cF
    c.xi
    cK
    cV
    cW
    tchcph.f
    tchcph.h
    tchcph.v
    tchcph.k
    ipcl
    syl3anc
    #
    sseldd
    #
    addcld
    #
    abscld
    #
    readdcld
    wph
    @13
    @14
    @11
    caddc
    co
    #
    cr
    wph
    @3
    @11
    @5
    wph
    @3
    @28
    recnd
    #
    wph
    @11
    wph
    c2
    cr
    wcel
    #
    @10
    cr
    wcel
    #
    @11
    cr
    wcel
    2re
    wph
    @4
    @6
    wph
    @3
    @28
    wph
    @22
    cc0
    vx
    cv
    #
    @46
    c.xi
    co
    #
    cle
    wbr
    #
    vx
    cV
    wral
    #
    cc0
    @3
    cle
    wbr
    #
    tchcphlem1.3
    wph
    @48
    vx
    cV
    tchcph.4
    ralrimiva
    #
    @48
    @50
    vx
    cX
    cV
    @46
    cX
    wceq
    #
    @47
    @3
    cc0
    cle
    @52
    @47
    @3
    wceq
    @46
    cX
    @46
    cX
    c.xi
    oveq12
    anidms
    breq2d
    rspcv
    sylc
    #
    resqrtcld
    #
    wph
    @5
    @29
    wph
    @23
    @49
    cc0
    @5
    cle
    wbr
    #
    tchcphlem1.4
    @51
    @48
    @55
    vx
    cY
    cV
    @46
    cY
    wceq
    #
    @47
    @5
    cc0
    cle
    @56
    @47
    @5
    wceq
    @46
    cY
    @46
    cY
    c.xi
    oveq12
    anidms
    breq2d
    rspcv
    sylc
    #
    resqrtcld
    #
    remulcld
    #
    c2
    @10
    remulcl
    sylancr
    #
    recnd
    wph
    @5
    @29
    recnd
    #
    add32d
    #
    wph
    @14
    @11
    @30
    @60
    readdcld
    eqeltrd
    wph
    @1
    @14
    cabs
    cfv
    #
    @18
    caddc
    co
    #
    @19
    cle
    wph
    @1
    @14
    @17
    cmin
    co
    #
    cabs
    cfv
    #
    @64
    cle
    wph
    @1
    cabs
    cfv
    @1
    @66
    wph
    @1
    @27
    wph
    @20
    @49
    cc0
    @1
    cle
    wbr
    #
    @26
    @51
    @48
    @67
    vx
    @0
    cV
    @46
    @0
    wceq
    #
    @47
    @1
    cc0
    cle
    @68
    @47
    @1
    wceq
    @46
    @0
    @46
    @0
    c.xi
    oveq12
    anidms
    breq2d
    rspcv
    sylc
    #
    absidd
    wph
    @1
    @65
    cabs
    wph
    @14
    @17
    cF
    csg
    cfv
    #
    co
    #
    @3
    @5
    cF
    cplusg
    cfv
    #
    co
    #
    @15
    @16
    @72
    co
    #
    @70
    co
    @65
    @1
    wph
    @14
    @73
    @17
    @74
    @70
    wph
    caddc
    @72
    @3
    @5
    wph
    @31
    caddc
    @72
    wceq
    @32
    cF
    cW
    tchcph.f
    clmadd
    syl
    #
    oveqd
    wph
    caddc
    @72
    @15
    @16
    @75
    oveqd
    oveq12d
    wph
    @31
    @14
    cK
    wcel
    #
    @17
    cK
    wcel
    #
    @65
    @71
    wceq
    @32
    wph
    @31
    @3
    cK
    wcel
    #
    @5
    cK
    wcel
    #
    @76
    @32
    wph
    @24
    @22
    @22
    @78
    tchcph.1
    tchcphlem1.3
    tchcphlem1.3
    cX
    cX
    cF
    c.xi
    cK
    cV
    cW
    tchcph.f
    tchcph.h
    tchcph.v
    tchcph.k
    ipcl
    syl3anc
    wph
    @24
    @23
    @23
    @79
    tchcph.1
    tchcphlem1.4
    tchcphlem1.4
    cY
    cY
    cF
    c.xi
    cK
    cV
    cW
    tchcph.f
    tchcph.h
    tchcph.v
    tchcph.k
    ipcl
    syl3anc
    cF
    cK
    cW
    @3
    @5
    tchcph.f
    tchcph.k
    clmacl
    syl3anc
    #
    wph
    @31
    @34
    @37
    @77
    @32
    @35
    @38
    cF
    cK
    cW
    @15
    @16
    tchcph.f
    tchcph.k
    clmacl
    syl3anc
    @14
    @17
    cF
    cK
    cW
    tchcph.f
    tchcph.k
    clmsub
    syl3anc
    wph
    cX
    cY
    cX
    cY
    @72
    @70
    cF
    c.xi
    c.mi
    cV
    cW
    tchcph.f
    tchcph.h
    tchcph.v
    tchcph.m
    @70
    eqid
    @72
    eqid
    tchcph.1
    tchcphlem1.3
    tchcphlem1.4
    tchcphlem1.3
    tchcphlem1.4
    ip2subdi
    3eqtr4rd
    fveq2d
    eqtr3d
    wph
    @14
    @17
    wph
    cK
    cc
    @14
    @33
    @80
    sseldd
    @40
    abs2dif2d
    eqbrtrd
    wph
    @63
    @14
    @18
    caddc
    wph
    @14
    @30
    wph
    @3
    @5
    @28
    @29
    @53
    @57
    addge0d
    absidd
    oveq1d
    breqtrd
    wph
    @19
    @42
    @13
    cle
    wph
    @18
    @11
    @14
    @41
    @60
    @30
    wph
    @18
    c2
    @15
    cabs
    cfv
    #
    cmul
    co
    #
    @11
    @41
    wph
    @44
    @81
    cr
    wcel
    #
    @82
    cr
    wcel
    2re
    wph
    @15
    @36
    abscld
    #
    c2
    @81
    remulcl
    sylancr
    @60
    wph
    @18
    @81
    @16
    cabs
    cfv
    #
    caddc
    co
    #
    @82
    cle
    wph
    @15
    @16
    @36
    @39
    abstrid
    wph
    @82
    @81
    @81
    caddc
    co
    @86
    wph
    @81
    wph
    @81
    @84
    recnd
    2timesd
    wph
    @81
    @85
    @81
    caddc
    wph
    @15
    ccj
    cfv
    #
    cabs
    cfv
    @81
    @85
    wph
    @15
    @36
    abscjd
    wph
    @87
    @16
    cabs
    wph
    @87
    @15
    cF
    cstv
    cfv
    #
    cfv
    #
    @16
    wph
    @15
    ccj
    @88
    wph
    @31
    ccj
    @88
    wceq
    @32
    cF
    cW
    tchcph.f
    clmcj
    syl
    fveq1d
    wph
    @24
    @22
    @23
    @89
    @16
    wceq
    tchcph.1
    tchcphlem1.3
    tchcphlem1.4
    cX
    cY
    cF
    c.xi
    @88
    cV
    cW
    tchcph.f
    tchcph.h
    tchcph.v
    @88
    eqid
    ipcj
    syl3anc
    eqtrd
    fveq2d
    eqtr3d
    oveq2d
    eqtrd
    breqtrrd
    wph
    @81
    @10
    cle
    wbr
    #
    @82
    @11
    cle
    wbr
    #
    wph
    @81
    cX
    cG
    cnm
    cfv
    #
    cfv
    #
    cY
    @92
    cfv
    #
    cmul
    co
    @10
    cle
    wph
    vx
    @16
    @5
    cdiv
    co
    #
    cF
    cG
    c.xi
    cK
    @92
    cV
    cW
    cX
    cY
    tchval.n
    tchcph.v
    tchcph.f
    tchcph.1
    tchcph.2
    tchcph.h
    tchcph.3
    tchcph.4
    tchcph.k
    @92
    eqid
    #
    @95
    eqid
    tchcphlem1.3
    tchcphlem1.4
    ipcau2
    wph
    @93
    @4
    @94
    @6
    cmul
    wph
    @21
    @22
    @93
    @4
    wceq
    @25
    tchcphlem1.3
    cG
    c.xi
    @92
    cV
    cW
    cX
    tchval.n
    @96
    tchcph.v
    tchcph.h
    tchnmval
    syl2anc
    wph
    @21
    @23
    @94
    @6
    wceq
    @25
    tchcphlem1.4
    cG
    c.xi
    @92
    cV
    cW
    cY
    tchval.n
    @96
    tchcph.v
    tchcph.h
    tchnmval
    syl2anc
    oveq12d
    breqtrd
    wph
    @83
    @45
    @44
    cc0
    c2
    clt
    wbr
    #
    @90
    @91
    wb
    @84
    @59
    @44
    wph
    2re
    a1i
    @97
    wph
    2pos
    a1i
    @81
    @10
    c2
    lemul2
    syl112anc
    mpbid
    letrd
    leadd2dd
    @62
    breqtrrd
    letrd
    wph
    @1
    wph
    @1
    @27
    recnd
    sqsqrtd
    wph
    @9
    @4
    c2
    cexp
    co
    #
    @11
    caddc
    co
    #
    @6
    c2
    cexp
    co
    #
    caddc
    co
    #
    @13
    wph
    @4
    cc
    wcel
    @6
    cc
    wcel
    @9
    @101
    wceq
    wph
    @3
    @43
    sqrtcld
    wph
    @6
    @58
    recnd
    @4
    @6
    binom2
    syl2anc
    wph
    @99
    @12
    @100
    @5
    caddc
    wph
    @98
    @3
    @11
    caddc
    wph
    @3
    @43
    sqsqrtd
    oveq1d
    wph
    @5
    @61
    sqsqrtd
    oveq12d
    eqtrd
    3brtr4d
    wph
    @2
    @7
    wph
    @1
    @27
    @69
    resqrtcld
    wph
    @4
    @6
    @54
    @58
    readdcld
    wph
    @1
    @27
    @69
    sqrtge0d
    wph
    @4
    @6
    @54
    @58
    wph
    @3
    @28
    @53
    sqrtge0d
    wph
    @5
    @29
    @57
    sqrtge0d
    addge0d
    le2sqd
    mpbird
end
