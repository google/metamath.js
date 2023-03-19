include "crg.mm"
include "wcel.mm"
include "cfv.mm"
include "cmulr.mm"
include "co.mm"
include "cbs.mm"
include "wceq.mm"
include "cui.mm"
include "eqid.mm"
include "1unit.mm"
include "ringinvcl.mm"
include "mpdan.mm"
include "ringlidm.mm"
include "unitrinv.mm"
include "eqtr3d.mm"

theorem 1rinv
  let cR: class R
  let c.1: class .1.
  let cI: class I
  assume 1rinv.1: |- I = ( invr ` R )
  assume 1rinv.2: |- .1. = ( 1r ` R )


  assert |- ( R e. Ring -> ( I ` .1. ) = .1. )

  proof
    cR
    crg
    wcel
    #
    c.1
    c.1
    cI
    cfv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    @1
    c.1
    @0
    @1
    cR
    cbs
    cfv
    #
    wcel
    #
    @3
    @1
    wceq
    @0
    c.1
    cR
    cui
    cfv
    #
    wcel
    #
    @5
    cR
    @6
    c.1
    @6
    eqid
    #
    1rinv.2
    1unit
    #
    @4
    cR
    @6
    cI
    c.1
    @8
    1rinv.1
    @4
    eqid
    #
    ringinvcl
    mpdan
    @4
    cR
    @2
    c.1
    @1
    @10
    @2
    eqid
    #
    1rinv.2
    ringlidm
    mpdan
    @0
    @7
    @3
    c.1
    wceq
    @9
    cR
    @2
    @6
    c.1
    cI
    c.1
    @8
    1rinv.1
    @11
    1rinv.2
    unitrinv
    mpdan
    eqtr3d
end
