include "wcel.mm"
include "cuhgr.mm"
include "cvtx.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "wa.mm"
include "wss.mm"
include "ciedg.mm"
include "wfun.mm"
include "cedg.mm"
include "csubgr.mm"
include "wbr.mm"
include "3simpa.mm"
include "0ss.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "3ad2ant3.mm"
include "eqid.mm"
include "uhgrfun.mm"
include "3ad2ant2.mm"
include "crn.mm"
include "edgval.mm"
include "wi.mm"
include "uhgr0vb.mm"
include "rneq.mm"
include "rn0.mm"
include "syl6eq.mm"
include "syl6bi.mm"
include "ex.mm"
include "pm2.43a.mm"
include "a1i.mm"
include "3imp.mm"
include "syl5eq.mm"
include "egrsubgr.mm"
include "syl112anc.mm"

theorem 0uhgrsubgr
  let cS: class S
  let cG: class G
  let cW: class W


  assert |- ( ( G e. W /\ S e. UHGraph /\ ( Vtx ` S ) = (/) ) -> S SubGraph G )

  proof
    cG
    cW
    wcel
    #
    cS
    cuhgr
    wcel
    #
    cS
    cvtx
    cfv
    #
    c0
    wceq
    #
    w3a
    #
    @0
    @1
    wa
    @2
    cG
    cvtx
    cfv
    #
    wss
    #
    cS
    ciedg
    cfv
    #
    wfun
    #
    cS
    cedg
    cfv
    #
    c0
    wceq
    cS
    cG
    csubgr
    wbr
    @0
    @1
    @3
    3simpa
    @3
    @0
    @6
    @1
    @3
    @6
    c0
    @5
    wss
    @5
    0ss
    @2
    c0
    @5
    sseq1
    mpbiri
    3ad2ant3
    @1
    @0
    @8
    @3
    @7
    cS
    @7
    eqid
    uhgrfun
    3ad2ant2
    @4
    @9
    @7
    crn
    #
    c0
    cS
    edgval
    @0
    @1
    @3
    @10
    c0
    wceq
    #
    @1
    @3
    @11
    wi
    wi
    @0
    @3
    @1
    @11
    @1
    @3
    @1
    @11
    wi
    @1
    @3
    wa
    @1
    @7
    c0
    wceq
    #
    @11
    cS
    cuhgr
    uhgr0vb
    @12
    @10
    c0
    crn
    c0
    @7
    c0
    rneq
    rn0
    syl6eq
    syl6bi
    ex
    pm2.43a
    a1i
    3imp
    syl5eq
    cS
    cuhgr
    cG
    cW
    egrsubgr
    syl112anc
end
