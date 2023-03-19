include "cv.mm"
include "ccid.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cop.mm"
include "wral.mm"
include "wa.mm"
include "cbs.mm"
include "wf.mm"
include "cxp.mm"
include "c1st.mm"
include "c2nd.mm"
include "chom.mm"
include "cmap.mm"
include "cixp.mm"
include "wcel.mm"
include "cfunc.mm"
include "wbr.mm"
include "w3a.mm"
include "eqid.mm"
include "ccat.mm"
include "df-br.mm"
include "sylib.mm"
include "funcrcl.mm"
include "syl.mm"
include "simpld.mm"
include "simprd.mm"
include "isfunc.mm"
include "mpbid.mm"
include "simp3d.mm"
include "adantr.mm"
include "ad2antrr.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "simplr.mm"
include "oveq12d.mm"
include "eleqtrrd.mm"
include "ad4antr.mm"
include "simp-5r.mm"
include "simp-4r.mm"
include "opeq12d.mm"
include "simpr.mm"
include "oveq123d.mm"
include "fveq12d.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "rspcdv.mm"
include "rspcimdv.mm"
include "adantld.mm"
include "mpd.mm"

theorem funcco
  let wph: wff ph
  let cB: class B
  let cD: class D
  let c.x: class .x.
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cN: class N
  let cO: class O
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume funcco.b: |- B = ( Base ` D )
  assume funcco.h: |- H = ( Hom ` D )
  assume funcco.o: |- .x. = ( comp ` D )
  assume funcco.O: |- O = ( comp ` E )
  assume funcco.f: |- ( ph -> F ( D Func E ) G )
  assume funcco.x: |- ( ph -> X e. B )
  assume funcco.y: |- ( ph -> Y e. B )
  assume funcco.z: |- ( ph -> Z e. B )
  assume funcco.m: |- ( ph -> M e. ( X H Y ) )
  assume funcco.n: |- ( ph -> N e. ( Y H Z ) )


  assert |- ( ph -> ( ( X G Z ) ` ( N ( <. X , Y >. .x. Z ) M ) ) = ( ( ( Y G Z ) ` N ) ( <. ( F ` X ) , ( F ` Y ) >. O ( F ` Z ) ) ( ( X G Y ) ` M ) ) )

  proof
    wph
    vx
    cv
    #
    cD
    ccid
    cfv
    #
    cfv
    @0
    @0
    cG
    co
    cfv
    @0
    cF
    cfv
    #
    cE
    ccid
    cfv
    #
    cfv
    wceq
    #
    vn
    cv
    #
    vm
    cv
    #
    @0
    vy
    cv
    #
    cop
    #
    vz
    cv
    #
    c.x
    co
    #
    co
    #
    @0
    @9
    cG
    co
    #
    cfv
    #
    @5
    @7
    @9
    cG
    co
    #
    cfv
    #
    @6
    @0
    @7
    cG
    co
    #
    cfv
    #
    @2
    @7
    cF
    cfv
    #
    cop
    #
    @9
    cF
    cfv
    #
    cO
    co
    #
    co
    #
    wceq
    #
    vn
    @7
    @9
    cH
    co
    #
    wral
    #
    vm
    @0
    @7
    cH
    co
    #
    wral
    #
    vz
    cB
    wral
    #
    vy
    cB
    wral
    #
    wa
    #
    vx
    cB
    wral
    #
    cN
    cM
    cX
    cY
    cop
    #
    cZ
    c.x
    co
    #
    co
    #
    cX
    cZ
    cG
    co
    #
    cfv
    #
    cN
    cY
    cZ
    cG
    co
    #
    cfv
    #
    cM
    cX
    cY
    cG
    co
    #
    cfv
    #
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    #
    cop
    #
    cZ
    cF
    cfv
    #
    cO
    co
    #
    co
    #
    wceq
    #
    wph
    cB
    cE
    cbs
    cfv
    #
    cF
    wf
    #
    cG
    vz
    cB
    cB
    cxp
    @9
    c1st
    cfv
    cF
    cfv
    @9
    c2nd
    cfv
    cF
    cfv
    cE
    chom
    cfv
    #
    co
    @9
    cH
    cfv
    cmap
    co
    cixp
    wcel
    #
    @31
    wph
    cF
    cG
    cD
    cE
    cfunc
    co
    #
    wbr
    #
    @49
    @51
    @31
    w3a
    funcco.f
    wph
    vx
    vy
    vz
    cB
    @48
    cD
    c.x
    @1
    vm
    vn
    cE
    cF
    cG
    cH
    @3
    @50
    cO
    funcco.b
    @48
    eqid
    funcco.h
    @50
    eqid
    @1
    eqid
    @3
    eqid
    funcco.o
    funcco.O
    wph
    cD
    ccat
    wcel
    #
    cE
    ccat
    wcel
    #
    wph
    cF
    cG
    cop
    #
    @52
    wcel
    #
    @54
    @55
    wa
    wph
    @53
    @57
    funcco.f
    cF
    cG
    @52
    df-br
    sylib
    cD
    cE
    @56
    funcrcl
    syl
    #
    simpld
    wph
    @54
    @55
    @58
    simprd
    isfunc
    mpbid
    simp3d
    wph
    @30
    @47
    vx
    cX
    cB
    funcco.x
    wph
    @0
    cX
    wceq
    #
    wa
    #
    @29
    @47
    @4
    @60
    @28
    @47
    vy
    cY
    cB
    wph
    cY
    cB
    wcel
    @59
    funcco.y
    adantr
    @60
    @7
    cY
    wceq
    #
    wa
    #
    @27
    @47
    vz
    cZ
    cB
    wph
    cZ
    cB
    wcel
    @59
    @61
    funcco.z
    ad2antrr
    @62
    @9
    cZ
    wceq
    #
    wa
    #
    @25
    @47
    vm
    cM
    @26
    @64
    cM
    cX
    cY
    cH
    co
    #
    @26
    wph
    cM
    @65
    wcel
    @59
    @61
    @63
    funcco.m
    ad3antrrr
    @64
    @0
    cX
    @7
    cY
    cH
    wph
    @59
    @61
    @63
    simpllr
    @60
    @61
    @63
    simplr
    oveq12d
    eleqtrrd
    @64
    @6
    cM
    wceq
    #
    wa
    #
    @23
    @47
    vn
    cN
    @24
    @67
    cN
    cY
    cZ
    cH
    co
    #
    @24
    wph
    cN
    @68
    wcel
    @59
    @61
    @63
    @66
    funcco.n
    ad4antr
    @67
    @7
    cY
    @9
    cZ
    cH
    @60
    @61
    @63
    @66
    simpllr
    @62
    @63
    @66
    simplr
    oveq12d
    eleqtrrd
    @67
    @5
    cN
    wceq
    #
    wa
    #
    @13
    @36
    @22
    @46
    @70
    @11
    @34
    @12
    @35
    @70
    @0
    cX
    @9
    cZ
    cG
    wph
    @59
    @61
    @63
    @66
    @69
    simp-5r
    #
    @62
    @63
    @66
    @69
    simpllr
    #
    oveq12d
    @70
    @5
    cN
    @6
    cM
    @10
    @33
    @70
    @8
    @32
    @9
    cZ
    c.x
    @70
    @0
    cX
    @7
    cY
    @71
    @60
    @61
    @63
    @66
    @69
    simp-4r
    #
    opeq12d
    @72
    oveq12d
    @67
    @69
    simpr
    #
    @64
    @66
    @69
    simplr
    #
    oveq123d
    fveq12d
    @70
    @15
    @38
    @17
    @40
    @21
    @45
    @70
    @19
    @43
    @20
    @44
    cO
    @70
    @2
    @41
    @18
    @42
    @70
    @0
    cX
    cF
    @71
    fveq2d
    @70
    @7
    cY
    cF
    @73
    fveq2d
    opeq12d
    @70
    @9
    cZ
    cF
    @72
    fveq2d
    oveq12d
    @70
    @5
    cN
    @14
    @37
    @70
    @7
    cY
    @9
    cZ
    cG
    @73
    @72
    oveq12d
    @74
    fveq12d
    @70
    @6
    cM
    @16
    @39
    @70
    @0
    cX
    @7
    cY
    cG
    @71
    @73
    oveq12d
    @75
    fveq12d
    oveq123d
    eqeq12d
    rspcdv
    rspcimdv
    rspcimdv
    rspcimdv
    adantld
    rspcimdv
    mpd
end
