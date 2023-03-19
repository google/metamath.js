include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "cress.mm"
include "co.mm"
include "c0g.mm"
include "cbs.mm"
include "cgrp.mm"
include "eqid.mm"
include "subggrp.mm"
include "grpidcl.mm"
include "syl.mm"
include "subg0.mm"
include "subgbas.mm"
include "3eltr4d.mm"

theorem subg0cl
  let cS: class S
  let cG: class G
  let c.0: class .0.
  assume subg0cl.i: |- .0. = ( 0g ` G )


  assert |- ( S e. ( SubGrp ` G ) -> .0. e. S )

  proof
    cS
    cG
    csubg
    cfv
    wcel
    #
    cG
    cS
    cress
    co
    #
    c0g
    cfv
    #
    @1
    cbs
    cfv
    #
    c.0
    cS
    @0
    @1
    cgrp
    wcel
    @2
    @3
    wcel
    cS
    cG
    @1
    @1
    eqid
    #
    subggrp
    @3
    @1
    @2
    @3
    eqid
    @2
    eqid
    grpidcl
    syl
    cS
    cG
    @1
    c.0
    @4
    subg0cl.i
    subg0
    cS
    cG
    @1
    @4
    subgbas
    3eltr4d
end
