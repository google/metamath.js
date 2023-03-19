include "ccrg.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cxp.mm"
include "ce1.mm"
include "cfv.mm"
include "crn.mm"
include "cpl1.mm"
include "cascl.mm"
include "eqid.mm"
include "evl1sca.mm"
include "cbs.mm"
include "wfn.mm"
include "cpws.mm"
include "co.mm"
include "crh.mm"
include "wf.mm"
include "evl1rhm.mm"
include "adantr.mm"
include "rhmf.mm"
include "ffn.mm"
include "3syl.mm"
include "crg.mm"
include "crngring.mm"
include "ply1sclf.mm"
include "syl.mm"
include "ffvelrn.mm"
include "sylancom.mm"
include "fnfvelrn.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"
include "syl6eleqr.mm"

theorem pf1const
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cX: class X
  assume pf1const.b: |- B = ( Base ` R )
  assume pf1const.q: |- Q = ran ( eval1 ` R )


  assert |- ( ( R e. CRing /\ X e. B ) -> ( B X. { X } ) e. Q )

  proof
    cR
    ccrg
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    cB
    cX
    csn
    cxp
    #
    cR
    ce1
    cfv
    #
    crn
    #
    cQ
    @2
    cX
    cR
    cpl1
    cfv
    #
    cascl
    cfv
    #
    cfv
    #
    @4
    cfv
    #
    @3
    @5
    @7
    cB
    @6
    cR
    @4
    cX
    @4
    eqid
    #
    @6
    eqid
    #
    pf1const.b
    @7
    eqid
    #
    evl1sca
    @2
    @4
    @6
    cbs
    cfv
    #
    wfn
    #
    @8
    @13
    wcel
    #
    @9
    @5
    wcel
    @2
    @4
    @6
    cR
    cB
    cpws
    co
    #
    crh
    co
    wcel
    #
    @13
    @16
    cbs
    cfv
    #
    @4
    wf
    @14
    @0
    @17
    @1
    cB
    @6
    cR
    @16
    @4
    @10
    @11
    @16
    eqid
    pf1const.b
    evl1rhm
    adantr
    @13
    @18
    @6
    @16
    @4
    @13
    eqid
    #
    @18
    eqid
    rhmf
    @13
    @18
    @4
    ffn
    3syl
    @0
    @1
    cB
    @13
    @7
    wf
    #
    @15
    @2
    cR
    crg
    wcel
    #
    @20
    @0
    @21
    @1
    cR
    crngring
    adantr
    @7
    @13
    @6
    cR
    cB
    @11
    @12
    pf1const.b
    @19
    ply1sclf
    syl
    cB
    @13
    cX
    @7
    ffvelrn
    sylancom
    @13
    @8
    @4
    fnfvelrn
    syl2anc
    eqeltrrd
    pf1const.q
    syl6eleqr
end
