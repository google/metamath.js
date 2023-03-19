include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "cgrp.mm"
include "cbs.mm"
include "wss.mm"
include "cress.mm"
include "co.mm"
include "csubg.mm"
include "crg.mm"
include "subrgrcl.mm"
include "ringgrp.mm"
include "syl.mm"
include "eqid.mm"
include "subrgss.mm"
include "subrgring.mm"
include "issubg.mm"
include "syl3anbrc.mm"

theorem subrgsubg
  let cA: class A
  let cR: class R


  assert |- ( A e. ( SubRing ` R ) -> A e. ( SubGrp ` R ) )

  proof
    cA
    cR
    csubrg
    cfv
    wcel
    #
    cR
    cgrp
    wcel
    #
    cA
    cR
    cbs
    cfv
    #
    wss
    cR
    cA
    cress
    co
    #
    cgrp
    wcel
    #
    cA
    cR
    csubg
    cfv
    wcel
    @0
    cR
    crg
    wcel
    @1
    cA
    cR
    subrgrcl
    cR
    ringgrp
    syl
    cA
    @2
    cR
    @2
    eqid
    #
    subrgss
    @0
    @3
    crg
    wcel
    @4
    cA
    cR
    @3
    @3
    eqid
    subrgring
    @3
    ringgrp
    syl
    @2
    cA
    cR
    @5
    issubg
    syl3anbrc
end
