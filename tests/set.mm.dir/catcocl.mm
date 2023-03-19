include "cv.mm"
include "cop.mm"
include "co.mm"
include "wcel.mm"
include "wral.mm"
include "ccat.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "iscat.mm"
include "ibi.mm"
include "simpl.mm"
include "2ralimi.mm"
include "adantl.mm"
include "ralimi.mm"
include "3syl.mm"
include "adantr.mm"
include "ad2antrr.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "simplr.mm"
include "oveq12d.mm"
include "eleqtrrd.mm"
include "simpr.mm"
include "simp-5r.mm"
include "simp-4r.mm"
include "opeq12d.mm"
include "oveq123d.mm"
include "eleq12d.mm"
include "rspcdv.mm"
include "rspcimdv.mm"
include "mpd.mm"

theorem catcocl
  let wph: wff ph
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cH: class H
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
  let cK: class K
  let cW: class W
  assume catcocl.b: |- B = ( Base ` C )
  assume catcocl.h: |- H = ( Hom ` C )
  assume catcocl.o: |- .x. = ( comp ` C )
  assume catcocl.c: |- ( ph -> C e. Cat )
  assume catcocl.x: |- ( ph -> X e. B )
  assume catcocl.y: |- ( ph -> Y e. B )
  assume catcocl.z: |- ( ph -> Z e. B )
  assume catcocl.f: |- ( ph -> F e. ( X H Y ) )
  assume catcocl.g: |- ( ph -> G e. ( Y H Z ) )


  assert |- ( ph -> ( G ( <. X , Y >. .x. Z ) F ) e. ( X H Z ) )

  proof
    wph
    vg
    cv
    #
    vf
    cv
    #
    vx
    cv
    #
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
    @2
    @5
    cH
    co
    #
    wcel
    #
    vg
    @3
    @5
    cH
    co
    #
    wral
    #
    vf
    @2
    @3
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
    vx
    cB
    wral
    #
    cG
    cF
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
    cH
    co
    #
    wcel
    #
    wph
    cC
    ccat
    wcel
    #
    @0
    @1
    @3
    @2
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
    wral
    @1
    @0
    @2
    @2
    cop
    @3
    c.x
    co
    co
    @1
    wceq
    vf
    @12
    wral
    wa
    vy
    cB
    wral
    vg
    @2
    @2
    cH
    co
    wrex
    #
    @9
    vv
    cv
    #
    @0
    @3
    @5
    cop
    vw
    cv
    #
    c.x
    co
    co
    @1
    @4
    @25
    c.x
    co
    co
    @24
    @7
    @2
    @5
    cop
    @25
    c.x
    co
    co
    wceq
    vv
    @5
    @25
    cH
    co
    wral
    vw
    cB
    wral
    #
    wa
    #
    vg
    @10
    wral
    vf
    @12
    wral
    #
    vz
    cB
    wral
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
    @16
    catcocl.c
    @22
    @31
    vx
    vy
    vz
    vw
    cB
    cC
    c.x
    vf
    vg
    vv
    cH
    ccat
    catcocl.b
    catcocl.h
    catcocl.o
    iscat
    ibi
    @30
    @15
    vx
    cB
    @29
    @15
    @23
    @28
    @13
    vy
    vz
    cB
    cB
    @27
    @9
    vf
    vg
    @12
    @10
    @9
    @26
    simpl
    2ralimi
    2ralimi
    adantl
    ralimi
    3syl
    wph
    @15
    @21
    vx
    cX
    cB
    catcocl.x
    wph
    @2
    cX
    wceq
    #
    wa
    #
    @14
    @21
    vy
    cY
    cB
    wph
    cY
    cB
    wcel
    @32
    catcocl.y
    adantr
    @33
    @3
    cY
    wceq
    #
    wa
    #
    @13
    @21
    vz
    cZ
    cB
    wph
    cZ
    cB
    wcel
    @32
    @34
    catcocl.z
    ad2antrr
    @35
    @5
    cZ
    wceq
    #
    wa
    #
    @11
    @21
    vf
    cF
    @12
    @37
    cF
    cX
    cY
    cH
    co
    #
    @12
    wph
    cF
    @38
    wcel
    @32
    @34
    @36
    catcocl.f
    ad3antrrr
    @37
    @2
    cX
    @3
    cY
    cH
    wph
    @32
    @34
    @36
    simpllr
    @33
    @34
    @36
    simplr
    #
    oveq12d
    eleqtrrd
    @37
    @1
    cF
    wceq
    #
    wa
    #
    @9
    @21
    vg
    cG
    @10
    @37
    cG
    @10
    wcel
    @40
    @37
    cG
    cY
    cZ
    cH
    co
    #
    @10
    wph
    cG
    @42
    wcel
    @32
    @34
    @36
    catcocl.g
    ad3antrrr
    @37
    @3
    cY
    @5
    cZ
    cH
    @39
    @35
    @36
    simpr
    oveq12d
    eleqtrrd
    adantr
    @41
    @0
    cG
    wceq
    #
    wa
    #
    @7
    @19
    @8
    @20
    @44
    @0
    cG
    @1
    cF
    @6
    @18
    @44
    @4
    @17
    @5
    cZ
    c.x
    @44
    @2
    cX
    @3
    cY
    wph
    @32
    @34
    @36
    @40
    @43
    simp-5r
    #
    @33
    @34
    @36
    @40
    @43
    simp-4r
    opeq12d
    @35
    @36
    @40
    @43
    simpllr
    #
    oveq12d
    @41
    @43
    simpr
    @37
    @40
    @43
    simplr
    oveq123d
    @44
    @2
    cX
    @5
    cZ
    cH
    @45
    @46
    oveq12d
    eleq12d
    rspcdv
    rspcimdv
    rspcimdv
    rspcimdv
    rspcimdv
    mpd
end
