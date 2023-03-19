include "cops.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "opoc1.mm"
include "cbs.mm"
include "wb.mm"
include "eqid.mm"
include "op1cl.mm"
include "op0cl.mm"
include "opcon1b.mm"
include "mpd3an23.mm"
include "mpbid.mm"

theorem opoc0
  let c.1: class .1.
  let cK: class K
  let c.pe: class ._|_
  let c.0: class .0.
  assume opoc1.z: |- .0. = ( 0. ` K )
  assume opoc1.u: |- .1. = ( 1. ` K )
  assume opoc1.o: |- ._|_ = ( oc ` K )


  assert |- ( K e. OP -> ( ._|_ ` .0. ) = .1. )

  proof
    cK
    cops
    wcel
    #
    c.1
    c.pe
    cfv
    c.0
    wceq
    #
    c.0
    c.pe
    cfv
    c.1
    wceq
    #
    c.1
    cK
    c.pe
    c.0
    opoc1.z
    opoc1.u
    opoc1.o
    opoc1
    @0
    c.1
    cK
    cbs
    cfv
    #
    wcel
    c.0
    @3
    wcel
    @1
    @2
    wb
    @3
    c.1
    cK
    @3
    eqid
    #
    opoc1.u
    op1cl
    @3
    cK
    c.0
    @4
    opoc1.z
    op0cl
    @3
    cK
    c.pe
    c.1
    c.0
    @4
    opoc1.o
    opcon1b
    mpd3an23
    mpbid
end
