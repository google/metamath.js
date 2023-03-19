include "cphl.mm"
include "wcel.mm"
include "c0.mm"
include "clspn.mm"
include "cfv.mm"
include "csn.mm"
include "clmod.mm"
include "wceq.mm"
include "phllmod.mm"
include "eqid.mm"
include "lsp0.mm"
include "syl.mm"
include "fveq2d.mm"
include "wss.mm"
include "0ss.mm"
include "ocvlsp.mm"
include "mpan2.mm"
include "ocv0.mm"
include "syl6eq.mm"
include "eqtr3d.mm"

theorem ocvz
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume ocvz.v: |- V = ( Base ` W )
  assume ocvz.o: |- ._|_ = ( ocv ` W )
  assume ocvz.z: |- .0. = ( 0g ` W )


  assert |- ( W e. PreHil -> ( ._|_ ` { .0. } ) = V )

  proof
    cW
    cphl
    wcel
    #
    c0
    cW
    clspn
    cfv
    #
    cfv
    #
    c.pe
    cfv
    #
    c.0
    csn
    #
    c.pe
    cfv
    cV
    @0
    @2
    @4
    c.pe
    @0
    cW
    clmod
    wcel
    @2
    @4
    wceq
    cW
    phllmod
    @1
    cW
    c.0
    ocvz.z
    @1
    eqid
    #
    lsp0
    syl
    fveq2d
    @0
    @3
    c0
    c.pe
    cfv
    #
    cV
    @0
    c0
    cV
    wss
    @3
    @6
    wceq
    cV
    0ss
    c0
    @1
    c.pe
    cV
    cW
    ocvz.v
    ocvz.o
    @5
    ocvlsp
    mpan2
    c.pe
    cV
    cW
    ocvz.v
    ocvz.o
    ocv0
    syl6eq
    eqtr3d
end
