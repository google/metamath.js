include "cops.mm"
include "wcel.mm"
include "cfv.mm"
include "cple.mm"
include "wbr.mm"
include "wceq.mm"
include "cbs.mm"
include "eqid.mm"
include "op0cl.mm"
include "opoccl.mm"
include "mpdan.mm"
include "ople1.mm"
include "wb.mm"
include "op1cl.mm"
include "oplecon1b.mm"
include "mpd3an23.mm"
include "mpbird.mm"
include "ople0.mm"
include "mpbid.mm"

theorem opoc1
  let c.1: class .1.
  let cK: class K
  let c.pe: class ._|_
  let c.0: class .0.
  assume opoc1.z: |- .0. = ( 0. ` K )
  assume opoc1.u: |- .1. = ( 1. ` K )
  assume opoc1.o: |- ._|_ = ( oc ` K )


  assert |- ( K e. OP -> ( ._|_ ` .1. ) = .0. )

  proof
    cK
    cops
    wcel
    #
    c.1
    c.pe
    cfv
    #
    c.0
    cK
    cple
    cfv
    #
    wbr
    #
    @1
    c.0
    wceq
    #
    @0
    @3
    c.0
    c.pe
    cfv
    #
    c.1
    @2
    wbr
    #
    @0
    @5
    cK
    cbs
    cfv
    #
    wcel
    #
    @6
    @0
    c.0
    @7
    wcel
    #
    @8
    @7
    cK
    c.0
    @7
    eqid
    #
    opoc1.z
    op0cl
    #
    @7
    cK
    c.pe
    c.0
    @10
    opoc1.o
    opoccl
    mpdan
    @7
    c.1
    cK
    @2
    @5
    @10
    @2
    eqid
    #
    opoc1.u
    ople1
    mpdan
    @0
    c.1
    @7
    wcel
    #
    @9
    @3
    @6
    wb
    @7
    c.1
    cK
    @10
    opoc1.u
    op1cl
    #
    @11
    @7
    cK
    @2
    c.pe
    c.1
    c.0
    @10
    @12
    opoc1.o
    oplecon1b
    mpd3an23
    mpbird
    @0
    @1
    @7
    wcel
    #
    @3
    @4
    wb
    @0
    @13
    @15
    @14
    @7
    cK
    c.pe
    c.1
    @10
    opoc1.o
    opoccl
    mpdan
    @7
    cK
    @2
    @1
    c.0
    @10
    @12
    opoc1.z
    ople0
    mpdan
    mpbid
end
