include "chomf.mm"
include "cfv.mm"
include "ctpos.mm"
include "coppc.mm"
include "tposeqd.mm"
include "eqid.mm"
include "oppchomf.mm"
include "3eqtr3g.mm"

theorem oppchomfpropd
  let wph: wff ph
  let cC: class C
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume oppchomfpropd.1: |- ( ph -> ( Homf ` C ) = ( Homf ` D ) )


  assert |- ( ph -> ( Homf ` ( oppCat ` C ) ) = ( Homf ` ( oppCat ` D ) ) )

  proof
    wph
    cC
    chomf
    cfv
    #
    ctpos
    cD
    chomf
    cfv
    #
    ctpos
    cC
    coppc
    cfv
    #
    chomf
    cfv
    cD
    coppc
    cfv
    #
    chomf
    cfv
    wph
    @0
    @1
    oppchomfpropd.1
    tposeqd
    cC
    @0
    @2
    @2
    eqid
    @0
    eqid
    oppchomf
    cD
    @1
    @3
    @3
    eqid
    @1
    eqid
    oppchomf
    3eqtr3g
end
