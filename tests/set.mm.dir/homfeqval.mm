include "chomf.mm"
include "cfv.mm"
include "co.mm"
include "oveqd.mm"
include "eqid.mm"
include "homfval.mm"
include "cbs.mm"
include "homfeqbas.mm"
include "syl5eq.mm"
include "eleqtrd.mm"
include "3eqtr3d.mm"

theorem homfeqval
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cH: class H
  let cJ: class J
  let cX: class X
  let cY: class Y
  assume homfeqval.b: |- B = ( Base ` C )
  assume homfeqval.h: |- H = ( Hom ` C )
  assume homfeqval.j: |- J = ( Hom ` D )
  assume homfeqval.1: |- ( ph -> ( Homf ` C ) = ( Homf ` D ) )
  assume homfeqval.x: |- ( ph -> X e. B )
  assume homfeqval.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( X H Y ) = ( X J Y ) )

  proof
    wph
    cX
    cY
    cC
    chomf
    cfv
    #
    co
    cX
    cY
    cD
    chomf
    cfv
    #
    co
    cX
    cY
    cH
    co
    cX
    cY
    cJ
    co
    wph
    @0
    @1
    cX
    cY
    homfeqval.1
    oveqd
    wph
    cB
    cC
    @0
    cH
    cX
    cY
    @0
    eqid
    homfeqval.b
    homfeqval.h
    homfeqval.x
    homfeqval.y
    homfval
    wph
    cD
    cbs
    cfv
    #
    cD
    @1
    cJ
    cX
    cY
    @1
    eqid
    @2
    eqid
    homfeqval.j
    wph
    cX
    cB
    @2
    homfeqval.x
    wph
    cB
    cC
    cbs
    cfv
    @2
    homfeqval.b
    wph
    cC
    cD
    homfeqval.1
    homfeqbas
    syl5eq
    #
    eleqtrd
    wph
    cY
    cB
    @2
    homfeqval.y
    @3
    eleqtrd
    homfval
    3eqtr3d
end
