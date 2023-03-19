include "c0g.mm"
include "cfv.mm"
include "coppr.mm"
include "clmod.mm"
include "eqid.mm"
include "ldualsca.mm"
include "fveq2d.mm"
include "oppr0.mm"
include "3eqtr4g.mm"

theorem ldual0
  let wph: wff ph
  let cD: class D
  let cR: class R
  let cS: class S
  let cO: class O
  let cW: class W
  let c.0: class .0.
  assume ldual0.r: |- R = ( Scalar ` W )
  assume ldual0.z: |- .0. = ( 0g ` R )
  assume ldual0.d: |- D = ( LDual ` W )
  assume ldual0.s: |- S = ( Scalar ` D )
  assume ldual0.o: |- O = ( 0g ` S )
  assume ldual0.w: |- ( ph -> W e. LMod )


  assert |- ( ph -> O = .0. )

  proof
    wph
    cS
    c0g
    cfv
    cR
    coppr
    cfv
    #
    c0g
    cfv
    cO
    c.0
    wph
    cS
    @0
    c0g
    wph
    cD
    cS
    cR
    @0
    cW
    clmod
    ldual0.r
    @0
    eqid
    #
    ldual0.d
    ldual0.s
    ldual0.w
    ldualsca
    fveq2d
    ldual0.o
    cR
    @0
    c.0
    @1
    ldual0.z
    oppr0
    3eqtr4g
end
