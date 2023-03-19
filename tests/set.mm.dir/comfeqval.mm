include "cop.mm"
include "ccomf.mm"
include "cfv.mm"
include "co.mm"
include "oveqd.mm"
include "eqid.mm"
include "comfval.mm"
include "cbs.mm"
include "chom.mm"
include "homfeqbas.mm"
include "syl5eq.mm"
include "eleqtrd.mm"
include "homfeqval.mm"
include "3eqtr3d.mm"

theorem comfeqval
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let c.xb: class .xb
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume comfeqval.b: |- B = ( Base ` C )
  assume comfeqval.h: |- H = ( Hom ` C )
  assume comfeqval.1: |- .x. = ( comp ` C )
  assume comfeqval.2: |- .xb = ( comp ` D )
  assume comfeqval.3: |- ( ph -> ( Homf ` C ) = ( Homf ` D ) )
  assume comfeqval.4: |- ( ph -> ( comf ` C ) = ( comf ` D ) )
  assume comfeqval.x: |- ( ph -> X e. B )
  assume comfeqval.y: |- ( ph -> Y e. B )
  assume comfeqval.z: |- ( ph -> Z e. B )
  assume comfeqval.f: |- ( ph -> F e. ( X H Y ) )
  assume comfeqval.g: |- ( ph -> G e. ( Y H Z ) )


  assert |- ( ph -> ( G ( <. X , Y >. .x. Z ) F ) = ( G ( <. X , Y >. .xb Z ) F ) )

  proof
    wph
    cG
    cF
    cX
    cY
    cop
    #
    cZ
    cC
    ccomf
    cfv
    #
    co
    #
    co
    cG
    cF
    @0
    cZ
    cD
    ccomf
    cfv
    #
    co
    #
    co
    cG
    cF
    @0
    cZ
    c.x
    co
    co
    cG
    cF
    @0
    cZ
    c.xb
    co
    co
    wph
    @2
    @4
    cG
    cF
    wph
    @1
    @3
    @0
    cZ
    comfeqval.4
    oveqd
    oveqd
    wph
    cB
    cC
    c.x
    cF
    cG
    cH
    @1
    cX
    cY
    cZ
    @1
    eqid
    comfeqval.b
    comfeqval.h
    comfeqval.1
    comfeqval.x
    comfeqval.y
    comfeqval.z
    comfeqval.f
    comfeqval.g
    comfval
    wph
    cD
    cbs
    cfv
    #
    cD
    c.xb
    cF
    cG
    cD
    chom
    cfv
    #
    @3
    cX
    cY
    cZ
    @3
    eqid
    @5
    eqid
    @6
    eqid
    #
    comfeqval.2
    wph
    cX
    cB
    @5
    comfeqval.x
    wph
    cB
    cC
    cbs
    cfv
    @5
    comfeqval.b
    wph
    cC
    cD
    comfeqval.3
    homfeqbas
    syl5eq
    #
    eleqtrd
    wph
    cY
    cB
    @5
    comfeqval.y
    @8
    eleqtrd
    wph
    cZ
    cB
    @5
    comfeqval.z
    @8
    eleqtrd
    wph
    cF
    cX
    cY
    cH
    co
    cX
    cY
    @6
    co
    comfeqval.f
    wph
    cB
    cC
    cD
    cH
    @6
    cX
    cY
    comfeqval.b
    comfeqval.h
    @7
    comfeqval.3
    comfeqval.x
    comfeqval.y
    homfeqval
    eleqtrd
    wph
    cG
    cY
    cZ
    cH
    co
    cY
    cZ
    @6
    co
    comfeqval.g
    wph
    cB
    cC
    cD
    cH
    @6
    cY
    cZ
    comfeqval.b
    comfeqval.h
    @7
    comfeqval.3
    comfeqval.y
    comfeqval.z
    homfeqval
    eleqtrd
    comfval
    3eqtr3d
end
