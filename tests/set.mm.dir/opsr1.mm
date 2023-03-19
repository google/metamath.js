include "cbs.mm"
include "cfv.mm"
include "eqidd.mm"
include "opsrbas.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cmulr.mm"
include "opsrmulr.mm"
include "oveqdr.mm"
include "rngidpropd.mm"

theorem opsr1
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cT: class T
  let cI: class I
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  assume opsr0.s: |- S = ( I mPwSer R )
  assume opsr0.o: |- O = ( ( I ordPwSer R ) ` T )
  assume opsr0.t: |- ( ph -> T C_ ( I X. I ) )


  assert |- ( ph -> ( 1r ` S ) = ( 1r ` O ) )

  proof
    wph
    vx
    vy
    cS
    cbs
    cfv
    #
    cS
    cO
    wph
    @0
    eqidd
    wph
    cR
    cS
    cT
    cI
    cO
    opsr0.s
    opsr0.o
    opsr0.t
    opsrbas
    wph
    vx
    cv
    @0
    wcel
    vy
    cv
    @0
    wcel
    wa
    vx
    vy
    cS
    cmulr
    cfv
    cO
    cmulr
    cfv
    wph
    cR
    cS
    cT
    cI
    cO
    opsr0.s
    opsr0.o
    opsr0.t
    opsrmulr
    oveqdr
    rngidpropd
end
