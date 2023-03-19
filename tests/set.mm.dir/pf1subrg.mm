include "ccrg.mm"
include "wcel.mm"
include "ce1.mm"
include "cfv.mm"
include "cpl1.mm"
include "cbs.mm"
include "cima.mm"
include "cpws.mm"
include "co.mm"
include "csubrg.mm"
include "crn.mm"
include "crh.mm"
include "wf.mm"
include "wfn.mm"
include "wceq.mm"
include "eqid.mm"
include "evl1rhm.mm"
include "rhmf.mm"
include "ffn.mm"
include "fnima.mm"
include "4syl.mm"
include "syl6eqr.mm"
include "casa.mm"
include "crg.mm"
include "ply1assa.mm"
include "assaring.mm"
include "subrgid.mm"
include "3syl.mm"
include "rhmima.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"

theorem pf1subrg
  let cB: class B
  let cQ: class Q
  let cR: class R
  assume pf1const.b: |- B = ( Base ` R )
  assume pf1const.q: |- Q = ran ( eval1 ` R )


  assert |- ( R e. CRing -> Q e. ( SubRing ` ( R ^s B ) ) )

  proof
    cR
    ccrg
    wcel
    #
    cR
    ce1
    cfv
    #
    cR
    cpl1
    cfv
    #
    cbs
    cfv
    #
    cima
    #
    cQ
    cR
    cB
    cpws
    co
    #
    csubrg
    cfv
    #
    @0
    @4
    @1
    crn
    #
    cQ
    @0
    @1
    @2
    @5
    crh
    co
    wcel
    #
    @3
    @5
    cbs
    cfv
    #
    @1
    wf
    @1
    @3
    wfn
    @4
    @7
    wceq
    cB
    @2
    cR
    @5
    @1
    @1
    eqid
    @2
    eqid
    #
    @5
    eqid
    pf1const.b
    evl1rhm
    #
    @3
    @9
    @2
    @5
    @1
    @3
    eqid
    #
    @9
    eqid
    rhmf
    @3
    @9
    @1
    ffn
    @3
    @1
    fnima
    4syl
    pf1const.q
    syl6eqr
    @0
    @8
    @3
    @2
    csubrg
    cfv
    wcel
    #
    @4
    @6
    wcel
    @11
    @0
    @2
    casa
    wcel
    @2
    crg
    wcel
    @13
    @2
    cR
    @10
    ply1assa
    @2
    assaring
    @3
    @2
    @12
    subrgid
    3syl
    @1
    @2
    @5
    @3
    rhmima
    syl2anc
    eqeltrrd
end
