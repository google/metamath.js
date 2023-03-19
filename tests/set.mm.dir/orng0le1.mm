include "corng.mm"
include "wcel.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "cbs.mm"
include "wbr.mm"
include "crg.mm"
include "orngring.mm"
include "eqid.mm"
include "ringidcl.mm"
include "syl.mm"
include "orngsqr.mm"
include "mpdan.mm"
include "wceq.mm"
include "ringlidm.mm"
include "syl2anc.mm"
include "breqtrd.mm"

theorem orng0le1
  let c.1: class .1.
  let cF: class F
  let c.le: class .<_
  let c.0: class .0.
  assume orng0le1.1: |- .0. = ( 0g ` F )
  assume orng0le1.2: |- .1. = ( 1r ` F )
  assume orng0le1.3: |- .<_ = ( le ` F )


  assert |- ( F e. oRing -> .0. .<_ .1. )

  proof
    cF
    corng
    wcel
    #
    c.0
    c.1
    c.1
    cF
    cmulr
    cfv
    #
    co
    #
    c.1
    c.le
    @0
    c.1
    cF
    cbs
    cfv
    #
    wcel
    #
    c.0
    @2
    c.le
    wbr
    @0
    cF
    crg
    wcel
    #
    @4
    cF
    orngring
    #
    @3
    cF
    c.1
    @3
    eqid
    #
    orng0le1.2
    ringidcl
    syl
    #
    @3
    cF
    @1
    c.le
    c.1
    c.0
    @7
    orng0le1.3
    orng0le1.1
    @1
    eqid
    #
    orngsqr
    mpdan
    @0
    @5
    @4
    @2
    c.1
    wceq
    @6
    @8
    @3
    cF
    @1
    c.1
    c.1
    @7
    @9
    orng0le1.2
    ringlidm
    syl2anc
    breqtrd
end
