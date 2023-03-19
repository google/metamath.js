include "crg.mm"
include "wcel.mm"
include "cdsr.mm"
include "cfv.mm"
include "wbr.mm"
include "coppr.mm"
include "cbs.mm"
include "eqid.mm"
include "ringidcl.mm"
include "dvdsrid.mm"
include "mpdan.mm"
include "opprring.mm"
include "opprbas.mm"
include "syl2anc.mm"
include "isunit.mm"
include "sylanbrc.mm"

theorem 1unit
  let cR: class R
  let cU: class U
  let c.1: class .1.
  let c.pa: class .||
  let vr: setvar r
  let cE: class E
  assume unit.1: |- U = ( Unit ` R )
  assume unit.2: |- .1. = ( 1r ` R )


  assert |- ( R e. Ring -> .1. e. U )

  proof
    cR
    crg
    wcel
    #
    c.1
    c.1
    cR
    cdsr
    cfv
    #
    wbr
    #
    c.1
    c.1
    cR
    coppr
    cfv
    #
    cdsr
    cfv
    #
    wbr
    #
    c.1
    cU
    wcel
    @0
    c.1
    cR
    cbs
    cfv
    #
    wcel
    #
    @2
    @6
    cR
    c.1
    @6
    eqid
    #
    unit.2
    ringidcl
    #
    @6
    @1
    cR
    c.1
    @8
    @1
    eqid
    #
    dvdsrid
    mpdan
    @0
    @3
    crg
    wcel
    @7
    @5
    cR
    @3
    @3
    eqid
    #
    opprring
    @9
    @6
    @4
    @3
    c.1
    @6
    cR
    @3
    @11
    @8
    opprbas
    @4
    eqid
    #
    dvdsrid
    syl2anc
    @1
    cR
    @3
    cU
    c.1
    @4
    c.1
    unit.1
    unit.2
    @10
    @11
    @12
    isunit
    sylanbrc
end
