include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "cuhgr.mm"
include "ciedg.mm"
include "cdm.mm"
include "cpw.mm"
include "csn.mm"
include "cdif.mm"
include "wf.mm"
include "eqid.mm"
include "uhgrf.mm"
include "pweq.mm"
include "difeq1d.mm"
include "pw0.mm"
include "difeq1i.mm"
include "difid.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "adantl.mm"
include "feq3d.mm"
include "f00.mm"
include "simplbi.mm"
include "syl6bi.mm"
include "syl5.mm"
include "wi.mm"
include "simpl.mm"
include "simpr.mm"
include "uhgr0e.mm"
include "ex.mm"
include "adantr.mm"
include "impbid.mm"

theorem uhgr0vb
  let cG: class G
  let cW: class W


  assert |- ( ( G e. W /\ ( Vtx ` G ) = (/) ) -> ( G e. UHGraph <-> ( iEdg ` G ) = (/) ) )

  proof
    cG
    cW
    wcel
    #
    cG
    cvtx
    cfv
    #
    c0
    wceq
    #
    wa
    #
    cG
    cuhgr
    wcel
    #
    cG
    ciedg
    cfv
    #
    c0
    wceq
    #
    @4
    @5
    cdm
    #
    @1
    cpw
    #
    c0
    csn
    #
    cdif
    #
    @5
    wf
    #
    @3
    @6
    @5
    cG
    @1
    @1
    eqid
    @5
    eqid
    uhgrf
    @3
    @11
    @7
    c0
    @5
    wf
    #
    @6
    @3
    @10
    c0
    @5
    @7
    @2
    @10
    c0
    wceq
    @0
    @2
    @10
    c0
    cpw
    #
    @9
    cdif
    #
    c0
    @2
    @8
    @13
    @9
    @1
    c0
    pweq
    difeq1d
    @14
    @9
    @9
    cdif
    c0
    @13
    @9
    @9
    pw0
    difeq1i
    @9
    difid
    eqtri
    syl6eq
    adantl
    feq3d
    @12
    @6
    @7
    c0
    wceq
    @7
    @5
    f00
    simplbi
    syl6bi
    syl5
    @0
    @6
    @4
    wi
    @2
    @0
    @6
    @4
    @0
    @6
    wa
    cG
    cW
    @0
    @6
    simpl
    @0
    @6
    simpr
    uhgr0e
    ex
    adantr
    impbid
end
