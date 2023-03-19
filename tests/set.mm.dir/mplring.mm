include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "cmps.mm"
include "co.mm"
include "csubrg.mm"
include "eqid.mm"
include "simpl.mm"
include "simpr.mm"
include "mplsubrg.mm"
include "mplval2.mm"
include "subrgring.mm"
include "syl.mm"

theorem mplring
  let cP: class P
  let cR: class R
  let cI: class I
  let cV: class V
  assume mplgrp.p: |- P = ( I mPoly R )


  assert |- ( ( I e. V /\ R e. Ring ) -> P e. Ring )

  proof
    cI
    cV
    wcel
    #
    cR
    crg
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
    csubrg
    cfv
    wcel
    cP
    crg
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
    mplsubrg
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
    subrgring
    syl
end
