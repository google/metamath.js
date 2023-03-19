include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cmps.mm"
include "co.mm"
include "clmod.mm"
include "cbs.mm"
include "cfv.mm"
include "clss.mm"
include "eqid.mm"
include "simpl.mm"
include "simpr.mm"
include "psrlmod.mm"
include "mpllss.mm"
include "mplval2.mm"
include "lsslmod.mm"
include "syl2anc.mm"

theorem mpllmod
  let cP: class P
  let cR: class R
  let cI: class I
  let cV: class V
  assume mplgrp.p: |- P = ( I mPoly R )


  assert |- ( ( I e. V /\ R e. Ring ) -> P e. LMod )

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
    cI
    cR
    cmps
    co
    #
    clmod
    wcel
    cP
    cbs
    cfv
    #
    @3
    clss
    cfv
    #
    wcel
    cP
    clmod
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
    #
    psrlmod
    @2
    cP
    cR
    @3
    @4
    cI
    cV
    @6
    mplgrp.p
    @4
    eqid
    #
    @7
    @8
    mpllss
    @5
    @4
    @3
    cP
    cP
    cR
    @3
    @4
    cI
    mplgrp.p
    @6
    @9
    mplval2
    @5
    eqid
    lsslmod
    syl2anc
end
