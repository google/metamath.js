include "crg.mm"
include "wcel.mm"
include "cco1.mm"
include "cfv.mm"
include "cascl.mm"
include "cn0.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt.mm"
include "eqid.mm"
include "ply1scl1.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "cbs.mm"
include "ringidcl.mm"
include "coe1scl.mm"
include "mpdan.mm"
include "eqtrd.mm"

theorem coe1id
  let vx: setvar x
  let cP: class P
  let cR: class R
  let c.1: class .1.
  let cI: class I
  let c.0: class .0.
  let vk: setvar k
  assume coe1id.p: |- P = ( Poly1 ` R )
  assume coe1id.i: |- I = ( 1r ` P )
  assume coe1id.0: |- .0. = ( 0g ` R )
  assume coe1id.1: |- .1. = ( 1r ` R )

  disjoint P x
  disjoint R x
  disjoint .0. x
  disjoint .1. x
  disjoint k x
  assert |- ( R e. Ring -> ( coe1 ` I ) = ( x e. NN0 |-> if ( x = 0 , .1. , .0. ) ) )

  proof
    cR
    crg
    wcel
    #
    cI
    cco1
    cfv
    c.1
    cP
    cascl
    cfv
    #
    cfv
    #
    cco1
    cfv
    #
    vx
    cn0
    vx
    cv
    cc0
    wceq
    c.1
    c.0
    cif
    cmpt
    #
    @0
    cI
    @2
    cco1
    @0
    @2
    cI
    @1
    cP
    cR
    c.1
    cI
    coe1id.p
    @1
    eqid
    #
    coe1id.1
    coe1id.i
    ply1scl1
    eqcomd
    fveq2d
    @0
    c.1
    cR
    cbs
    cfv
    #
    wcel
    @3
    @4
    wceq
    @6
    cR
    c.1
    @6
    eqid
    #
    coe1id.1
    ringidcl
    vx
    @1
    cP
    cR
    @6
    c.1
    c.0
    coe1id.p
    @5
    @7
    coe1id.0
    coe1scl
    mpdan
    eqtrd
end
