include "cv.mm"
include "cop.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "wcel.mm"
include "ccat.mm"
include "iscat.mm"
include "ibi.mm"
include "syl.mm"
include "adantr.mm"
include "ad2antrr.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "simplr.mm"
include "oveq12d.mm"
include "eleqtrrd.mm"
include "ad4antr.mm"
include "ad5antr.mm"
include "ad6antr.mm"
include "simp-4r.mm"
include "simpr.mm"
include "simp-7r.mm"
include "simp-6r.mm"
include "opeq12d.mm"
include "simp-5r.mm"
include "oveq123d.mm"
include "eqeq12d.mm"
include "rspcdv.mm"
include "rspcimdv.mm"
include "adantld.mm"
include "mpd.mm"

theorem catass
  let wph: wff ph
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume catcocl.b: |- B = ( Base ` C )
  assume catcocl.h: |- H = ( Hom ` C )
  assume catcocl.o: |- .x. = ( comp ` C )
  assume catcocl.c: |- ( ph -> C e. Cat )
  assume catcocl.x: |- ( ph -> X e. B )
  assume catcocl.y: |- ( ph -> Y e. B )
  assume catcocl.z: |- ( ph -> Z e. B )
  assume catcocl.f: |- ( ph -> F e. ( X H Y ) )
  assume catcocl.g: |- ( ph -> G e. ( Y H Z ) )
  assume catass.w: |- ( ph -> W e. B )
  assume catass.g: |- ( ph -> K e. ( Z H W ) )


  assert |- ( ph -> ( ( K ( <. Y , Z >. .x. W ) G ) ( <. X , Y >. .x. W ) F ) = ( K ( <. X , Z >. .x. W ) ( G ( <. X , Y >. .x. Z ) F ) ) )

  proof
    wph
    vg
    cv
    #
    vf
    cv
    #
    vy
    cv
    #
    vx
    cv
    #
    cop
    @3
    c.x
    co
    co
    @1
    wceq
    vf
    @2
    @3
    cH
    co
    wral
    @1
    @0
    @3
    @3
    cop
    @2
    c.x
    co
    co
    @1
    wceq
    vf
    @3
    @2
    cH
    co
    #
    wral
    wa
    vy
    cB
    wral
    vg
    @3
    @3
    cH
    co
    wrex
    #
    @0
    @1
    @3
    @2
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
    @3
    @7
    cH
    co
    wcel
    #
    vk
    cv
    #
    @0
    @2
    @7
    cop
    #
    vw
    cv
    #
    c.x
    co
    #
    co
    #
    @1
    @6
    @13
    c.x
    co
    #
    co
    #
    @11
    @9
    @3
    @7
    cop
    #
    @13
    c.x
    co
    #
    co
    #
    wceq
    #
    vk
    @7
    @13
    cH
    co
    #
    wral
    #
    vw
    cB
    wral
    #
    wa
    #
    vg
    @2
    @7
    cH
    co
    #
    wral
    #
    vf
    @4
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
    cK
    cG
    cY
    cZ
    cop
    #
    cW
    c.x
    co
    #
    co
    #
    cF
    cX
    cY
    cop
    #
    cW
    c.x
    co
    #
    co
    #
    cK
    cG
    cF
    @36
    cZ
    c.x
    co
    #
    co
    #
    cX
    cZ
    cop
    #
    cW
    c.x
    co
    #
    co
    #
    wceq
    #
    wph
    cC
    ccat
    wcel
    #
    @32
    catcocl.c
    @45
    @32
    vx
    vy
    vz
    vw
    cB
    cC
    c.x
    vf
    vg
    vk
    cH
    ccat
    catcocl.b
    catcocl.h
    catcocl.o
    iscat
    ibi
    syl
    wph
    @31
    @44
    vx
    cX
    cB
    catcocl.x
    wph
    @3
    cX
    wceq
    #
    wa
    #
    @30
    @44
    @5
    @47
    @29
    @44
    vy
    cY
    cB
    wph
    cY
    cB
    wcel
    @46
    catcocl.y
    adantr
    @47
    @2
    cY
    wceq
    #
    wa
    #
    @28
    @44
    vz
    cZ
    cB
    wph
    cZ
    cB
    wcel
    @46
    @48
    catcocl.z
    ad2antrr
    @49
    @7
    cZ
    wceq
    #
    wa
    #
    @27
    @44
    vf
    cF
    @4
    @51
    cF
    cX
    cY
    cH
    co
    #
    @4
    wph
    cF
    @52
    wcel
    @46
    @48
    @50
    catcocl.f
    ad3antrrr
    @51
    @3
    cX
    @2
    cY
    cH
    wph
    @46
    @48
    @50
    simpllr
    @47
    @48
    @50
    simplr
    oveq12d
    eleqtrrd
    @51
    @1
    cF
    wceq
    #
    wa
    #
    @25
    @44
    vg
    cG
    @26
    @54
    cG
    cY
    cZ
    cH
    co
    #
    @26
    wph
    cG
    @55
    wcel
    @46
    @48
    @50
    @53
    catcocl.g
    ad4antr
    @54
    @2
    cY
    @7
    cZ
    cH
    @47
    @48
    @50
    @53
    simpllr
    @49
    @50
    @53
    simplr
    oveq12d
    eleqtrrd
    @54
    @0
    cG
    wceq
    #
    wa
    #
    @24
    @44
    @10
    @57
    @23
    @44
    vw
    cW
    cB
    wph
    cW
    cB
    wcel
    @46
    @48
    @50
    @53
    @56
    catass.w
    ad5antr
    @57
    @13
    cW
    wceq
    #
    wa
    #
    @21
    @44
    vk
    cK
    @22
    @59
    cK
    cZ
    cW
    cH
    co
    #
    @22
    wph
    cK
    @60
    wcel
    @46
    @48
    @50
    @53
    @56
    @58
    catass.g
    ad6antr
    @59
    @7
    cZ
    @13
    cW
    cH
    @49
    @50
    @53
    @56
    @58
    simp-4r
    @57
    @58
    simpr
    oveq12d
    eleqtrrd
    @59
    @11
    cK
    wceq
    #
    wa
    #
    @17
    @38
    @20
    @43
    @62
    @15
    @35
    @1
    cF
    @16
    @37
    @62
    @6
    @36
    @13
    cW
    c.x
    @62
    @3
    cX
    @2
    cY
    wph
    @46
    @48
    @50
    @53
    @56
    @58
    @61
    simp-7r
    #
    @47
    @48
    @50
    @53
    @56
    @58
    @61
    simp-6r
    #
    opeq12d
    #
    @57
    @58
    @61
    simplr
    #
    oveq12d
    @62
    @11
    cK
    @0
    cG
    @14
    @34
    @62
    @12
    @33
    @13
    cW
    c.x
    @62
    @2
    cY
    @7
    cZ
    @64
    @49
    @50
    @53
    @56
    @58
    @61
    simp-5r
    #
    opeq12d
    @66
    oveq12d
    @59
    @61
    simpr
    #
    @54
    @56
    @58
    @61
    simpllr
    #
    oveq123d
    @51
    @53
    @56
    @58
    @61
    simp-4r
    #
    oveq123d
    @62
    @11
    cK
    @9
    @40
    @19
    @42
    @62
    @18
    @41
    @13
    cW
    c.x
    @62
    @3
    cX
    @7
    cZ
    @63
    @67
    opeq12d
    @66
    oveq12d
    @68
    @62
    @0
    cG
    @1
    cF
    @8
    @39
    @62
    @6
    @36
    @7
    cZ
    c.x
    @65
    @67
    oveq12d
    @69
    @70
    oveq123d
    oveq123d
    eqeq12d
    rspcdv
    rspcimdv
    adantld
    rspcimdv
    rspcimdv
    rspcimdv
    rspcimdv
    adantld
    rspcimdv
    mpd
end
