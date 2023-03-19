include "cur.mm"
include "cfv.mm"
include "coppr.mm"
include "clmod.mm"
include "eqid.mm"
include "ldualsca.mm"
include "fveq2d.mm"
include "oppr1.mm"
include "3eqtr4g.mm"

theorem ldual1
  let wph: wff ph
  let cD: class D
  let cR: class R
  let cS: class S
  let c.1: class .1.
  let cI: class I
  let cW: class W
  assume ldual1.r: |- R = ( Scalar ` W )
  assume ldual1.u: |- .1. = ( 1r ` R )
  assume ldual1.d: |- D = ( LDual ` W )
  assume ldual1.s: |- S = ( Scalar ` D )
  assume ldual1.i: |- I = ( 1r ` S )
  assume ldual1.w: |- ( ph -> W e. LMod )


  assert |- ( ph -> I = .1. )

  proof
    wph
    cS
    cur
    cfv
    cR
    coppr
    cfv
    #
    cur
    cfv
    cI
    c.1
    wph
    cS
    @0
    cur
    wph
    cD
    cS
    cR
    @0
    cW
    clmod
    ldual1.r
    @0
    eqid
    #
    ldual1.d
    ldual1.s
    ldual1.w
    ldualsca
    fveq2d
    ldual1.i
    cR
    c.1
    @0
    @1
    ldual1.u
    oppr1
    3eqtr4g
end
