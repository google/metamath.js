include "wcel.mm"
include "ccrg.mm"
include "wa.mm"
include "casa.mm"
include "cbs.mm"
include "cfv.mm"
include "cmps.mm"
include "co.mm"
include "csubrg.mm"
include "clss.mm"
include "eqid.mm"
include "simpl.mm"
include "crg.mm"
include "crngring.mm"
include "adantl.mm"
include "mplsubrg.mm"
include "mpllss.mm"
include "cur.mm"
include "wss.mm"
include "wb.mm"
include "simpr.mm"
include "psrassa.mm"
include "subrg1cl.mm"
include "syl.mm"
include "subrgss.mm"
include "mplval2.mm"
include "issubassa.mm"
include "syl3anc.mm"
include "mpbir2and.mm"

theorem mplassa
  let cP: class P
  let cR: class R
  let cI: class I
  let cV: class V
  assume mplgrp.p: |- P = ( I mPoly R )


  assert |- ( ( I e. V /\ R e. CRing ) -> P e. AssAlg )

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
    cP
    casa
    wcel
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
    #
    @4
    @5
    clss
    cfv
    #
    wcel
    #
    @2
    cP
    cR
    @5
    @4
    cI
    cV
    @5
    eqid
    #
    mplgrp.p
    @4
    eqid
    #
    @0
    @1
    simpl
    #
    @1
    cR
    crg
    wcel
    @0
    cR
    crngring
    adantl
    #
    mplsubrg
    #
    @2
    cP
    cR
    @5
    @4
    cI
    cV
    @9
    mplgrp.p
    @10
    @11
    @12
    mpllss
    @2
    @5
    casa
    wcel
    @5
    cur
    cfv
    #
    @4
    wcel
    #
    @4
    @5
    cbs
    cfv
    #
    wss
    #
    @3
    @6
    @8
    wa
    wb
    @2
    cR
    @5
    cI
    cV
    @9
    @11
    @0
    @1
    simpr
    psrassa
    @2
    @6
    @15
    @13
    @4
    @5
    @14
    @14
    eqid
    #
    subrg1cl
    syl
    @2
    @6
    @17
    @13
    @4
    @16
    @5
    @16
    eqid
    #
    subrgss
    syl
    @4
    cP
    @14
    @7
    @16
    @5
    cP
    cR
    @5
    @4
    cI
    mplgrp.p
    @9
    @10
    mplval2
    @7
    eqid
    @19
    @18
    issubassa
    syl3anc
    mpbir2and
end
