include "cphl.mm"
include "wcel.mm"
include "cfv.mm"
include "cin.mm"
include "csn.mm"
include "wss.mm"
include "wceq.mm"
include "ocvss.mm"
include "sseqin2.mm"
include "mpbi.mm"
include "clss.mm"
include "clmod.mm"
include "phllmod.mm"
include "eqid.mm"
include "lss1.mm"
include "syl.mm"
include "ocvin.mm"
include "mpdan.mm"
include "syl5eqr.mm"

theorem ocv1
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume ocvz.v: |- V = ( Base ` W )
  assume ocvz.o: |- ._|_ = ( ocv ` W )
  assume ocvz.z: |- .0. = ( 0g ` W )


  assert |- ( W e. PreHil -> ( ._|_ ` V ) = { .0. } )

  proof
    cW
    cphl
    wcel
    #
    cV
    c.pe
    cfv
    #
    cV
    @1
    cin
    #
    c.0
    csn
    #
    @1
    cV
    wss
    @2
    @1
    wceq
    cV
    c.pe
    cV
    cW
    ocvz.v
    ocvz.o
    ocvss
    @1
    cV
    sseqin2
    mpbi
    @0
    cV
    cW
    clss
    cfv
    #
    wcel
    #
    @2
    @3
    wceq
    @0
    cW
    clmod
    wcel
    @5
    cW
    phllmod
    @4
    cV
    cW
    ocvz.v
    @4
    eqid
    #
    lss1
    syl
    cV
    @4
    c.pe
    cW
    c.0
    ocvz.o
    @6
    ocvz.z
    ocvin
    mpdan
    syl5eqr
end
