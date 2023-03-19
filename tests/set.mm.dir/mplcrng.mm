include "wcel.mm"
include "ccrg.mm"
include "wa.mm"
include "cmps.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "csubrg.mm"
include "eqid.mm"
include "simpl.mm"
include "simpr.mm"
include "psrcrng.mm"
include "crg.mm"
include "crngring.mm"
include "adantl.mm"
include "mplsubrg.mm"
include "mplval2.mm"
include "subrgcrng.mm"
include "syl2anc.mm"

theorem mplcrng
  let cP: class P
  let cR: class R
  let cI: class I
  let cV: class V
  assume mplgrp.p: |- P = ( I mPoly R )


  assert |- ( ( I e. V /\ R e. CRing ) -> P e. CRing )

  proof
    cI
    cV
    wcel
    #
    cR
    ccrg
    wcel
    #
    wa
    #
    cI
    cR
    cmps
    co
    #
    ccrg
    wcel
    cP
    cbs
    cfv
    #
    @3
    csubrg
    cfv
    wcel
    cP
    ccrg
    wcel
    @2
    cR
    @3
    cI
    cV
    @3
    eqid
    #
    @0
    @1
    simpl
    #
    @0
    @1
    simpr
    psrcrng
    @2
    cP
    cR
    @3
    @4
    cI
    cV
    @5
    mplgrp.p
    @4
    eqid
    #
    @6
    @1
    cR
    crg
    wcel
    @0
    cR
    crngring
    adantl
    mplsubrg
    @4
    @3
    cP
    cP
    cR
    @3
    @4
    cI
    mplgrp.p
    @5
    @7
    mplval2
    subrgcrng
    syl2anc
end
