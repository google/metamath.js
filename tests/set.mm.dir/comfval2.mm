include "chom.mm"
include "cfv.mm"
include "eqid.mm"
include "co.mm"
include "homfval.mm"
include "eleqtrd.mm"
include "comfval.mm"

theorem comfval2
  let wph: wff ph
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cH: class H
  let cO: class O
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  assume comfffval2.o: |- O = ( comf ` C )
  assume comfffval2.b: |- B = ( Base ` C )
  assume comfffval2.h: |- H = ( Homf ` C )
  assume comfffval2.x: |- .x. = ( comp ` C )
  assume comffval2.x: |- ( ph -> X e. B )
  assume comffval2.y: |- ( ph -> Y e. B )
  assume comffval2.z: |- ( ph -> Z e. B )
  assume comfval2.f: |- ( ph -> F e. ( X H Y ) )
  assume comfval2.g: |- ( ph -> G e. ( Y H Z ) )


  assert |- ( ph -> ( G ( <. X , Y >. O Z ) F ) = ( G ( <. X , Y >. .x. Z ) F ) )

  proof
    wph
    cB
    cC
    c.x
    cF
    cG
    cC
    chom
    cfv
    #
    cO
    cX
    cY
    cZ
    comfffval2.o
    comfffval2.b
    @0
    eqid
    #
    comfffval2.x
    comffval2.x
    comffval2.y
    comffval2.z
    wph
    cF
    cX
    cY
    cH
    co
    cX
    cY
    @0
    co
    comfval2.f
    wph
    cB
    cC
    cH
    @0
    cX
    cY
    comfffval2.h
    comfffval2.b
    @1
    comffval2.x
    comffval2.y
    homfval
    eleqtrd
    wph
    cG
    cY
    cZ
    cH
    co
    cY
    cZ
    @0
    co
    comfval2.g
    wph
    cB
    cC
    cH
    @0
    cY
    cZ
    comfffval2.h
    comfffval2.b
    @1
    comffval2.y
    comffval2.z
    homfval
    eleqtrd
    comfval
end
