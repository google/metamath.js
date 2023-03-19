include "cbs.mm"
include "cfv.mm"
include "eqidd.mm"
include "opsrbas.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cplusg.mm"
include "opsrplusg.mm"
include "oveqdr.mm"
include "grpidpropd.mm"

theorem opsr0
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


  assert |- ( ph -> ( 0g ` S ) = ( 0g ` O ) )

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
    cplusg
    cfv
    cO
    cplusg
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
    opsrplusg
    oveqdr
    grpidpropd
end
