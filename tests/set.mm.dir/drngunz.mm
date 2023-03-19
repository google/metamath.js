include "cdr.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wne.mm"
include "cui.mm"
include "wa.mm"
include "crg.mm"
include "drngring.mm"
include "eqid.mm"
include "1unit.mm"
include "syl.mm"
include "drngunit.mm"
include "mpbid.mm"
include "simprd.mm"

theorem drngunz
  let cR: class R
  let c.1: class .1.
  let c.0: class .0.
  assume drngunz.z: |- .0. = ( 0g ` R )
  assume drngunz.u: |- .1. = ( 1r ` R )


  assert |- ( R e. DivRing -> .1. =/= .0. )

  proof
    cR
    cdr
    wcel
    #
    c.1
    cR
    cbs
    cfv
    #
    wcel
    #
    c.1
    c.0
    wne
    #
    @0
    c.1
    cR
    cui
    cfv
    #
    wcel
    #
    @2
    @3
    wa
    @0
    cR
    crg
    wcel
    @5
    cR
    drngring
    cR
    @4
    c.1
    @4
    eqid
    #
    drngunz.u
    1unit
    syl
    @1
    cR
    @4
    c.1
    c.0
    @1
    eqid
    @6
    drngunz.z
    drngunit
    mpbid
    simprd
end
