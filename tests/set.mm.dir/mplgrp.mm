include "wcel.mm"
include "cgrp.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "cmps.mm"
include "co.mm"
include "csubg.mm"
include "eqid.mm"
include "simpl.mm"
include "simpr.mm"
include "mplsubg.mm"
include "mplval2.mm"
include "subggrp.mm"
include "syl.mm"

theorem mplgrp
  let cP: class P
  let cR: class R
  let cI: class I
  let cV: class V
  assume mplgrp.p: |- P = ( I mPoly R )


  assert |- ( ( I e. V /\ R e. Grp ) -> P e. Grp )

  proof
    cI
    cV
    wcel
    #
    cR
    cgrp
    wcel
    #
    wa
    #
    cP
    cbs
    cfv
    #
    cI
    cR
    cmps
    co
    #
    csubg
    cfv
    wcel
    cP
    cgrp
    wcel
    @2
    cP
    cR
    @4
    @3
    cI
    cV
    @4
    eqid
    #
    mplgrp.p
    @3
    eqid
    #
    @0
    @1
    simpl
    @0
    @1
    simpr
    mplsubg
    @3
    @4
    cP
    cP
    cR
    @4
    @3
    cI
    mplgrp.p
    @5
    @6
    mplval2
    subggrp
    syl
end
