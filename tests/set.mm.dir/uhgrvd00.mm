include "cuhgr.mm"
include "wcel.mm"
include "cv.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wral.mm"
include "wn.mm"
include "c0.mm"
include "wa.mm"
include "wrex.mm"
include "eqid.mm"
include "vtxduhgr0edgnel.mm"
include "ralnex.mm"
include "syl6bbr.mm"
include "ralbidva.mm"
include "wne.mm"
include "ralcom.mm"
include "ralnex2.mm"
include "bitri.mm"
include "wex.mm"
include "simpr.mm"
include "cvtx.mm"
include "cpw.mm"
include "csn.mm"
include "cdif.mm"
include "cedg.mm"
include "eleq2i.mm"
include "uhgredgn0.mm"
include "sylan2b.mm"
include "eldifsn.mm"
include "wss.mm"
include "wi.mm"
include "elpwi.mm"
include "sseq2i.mm"
include "ssn0rex.mm"
include "ex.mm"
include "sylbir.mm"
include "syl.mm"
include "imp.mm"
include "sylbi.mm"
include "jca.mm"
include "eximdv.mm"
include "n0.mm"
include "df-rex.mm"
include "3imtr4g.mm"
include "con3d.mm"
include "syl5bi.mm"
include "nne.mm"
include "syl6ib.mm"
include "sylbid.mm"

theorem uhgrvd00
  let vv: setvar v
  let cE: class E
  let cG: class G
  let cV: class V
  let cU: class U
  let ve: setvar e
  assume vtxdusgradjvtx.v: |- V = ( Vtx ` G )
  assume vtxdusgradjvtx.e: |- E = ( Edg ` G )

  disjoint E v
  disjoint G v
  disjoint V v
  disjoint U v
  disjoint E e
  disjoint e v
  disjoint G e
  disjoint V e
  assert |- ( G e. UHGraph -> ( A. v e. V ( ( VtxDeg ` G ) ` v ) = 0 -> E = (/) ) )

  proof
    cG
    cuhgr
    wcel
    #
    vv
    cv
    #
    cG
    cvtxdg
    cfv
    #
    cfv
    cc0
    wceq
    #
    vv
    cV
    wral
    @1
    ve
    cv
    #
    wcel
    #
    wn
    #
    ve
    cE
    wral
    #
    vv
    cV
    wral
    #
    cE
    c0
    wceq
    #
    @0
    @3
    @7
    vv
    cV
    @0
    @1
    cV
    wcel
    wa
    @3
    @5
    ve
    cE
    wrex
    wn
    @7
    @2
    @1
    ve
    cE
    cG
    cV
    vtxdusgradjvtx.v
    vtxdusgradjvtx.e
    @2
    eqid
    vtxduhgr0edgnel
    @5
    ve
    cE
    ralnex
    syl6bbr
    ralbidva
    @0
    @8
    cE
    c0
    wne
    #
    wn
    #
    @9
    @8
    @5
    vv
    cV
    wrex
    #
    ve
    cE
    wrex
    #
    wn
    #
    @0
    @11
    @8
    @6
    vv
    cV
    wral
    ve
    cE
    wral
    @14
    @6
    vv
    ve
    cV
    cE
    ralcom
    @5
    ve
    vv
    cE
    cV
    ralnex2
    bitri
    @0
    @10
    @13
    @0
    @4
    cE
    wcel
    #
    ve
    wex
    @15
    @12
    wa
    #
    ve
    wex
    @10
    @13
    @0
    @15
    @16
    ve
    @0
    @15
    @16
    @0
    @15
    wa
    #
    @15
    @12
    @0
    @15
    simpr
    @17
    @4
    cG
    cvtx
    cfv
    #
    cpw
    #
    c0
    csn
    cdif
    wcel
    #
    @12
    @15
    @0
    @4
    cG
    cedg
    cfv
    #
    wcel
    @20
    cE
    @21
    @4
    vtxdusgradjvtx.e
    eleq2i
    @4
    cG
    uhgredgn0
    sylan2b
    @20
    @4
    @19
    wcel
    #
    @4
    c0
    wne
    #
    wa
    @12
    @4
    @19
    c0
    eldifsn
    @22
    @23
    @12
    @22
    @4
    @18
    wss
    #
    @23
    @12
    wi
    #
    @4
    @18
    elpwi
    @24
    @4
    cV
    wss
    #
    @25
    cV
    @18
    @4
    vtxdusgradjvtx.v
    sseq2i
    @26
    @23
    @12
    vv
    @4
    cV
    ssn0rex
    ex
    sylbir
    syl
    imp
    sylbi
    syl
    jca
    ex
    eximdv
    ve
    cE
    n0
    @12
    ve
    cE
    df-rex
    3imtr4g
    con3d
    syl5bi
    cE
    c0
    nne
    syl6ib
    sylbid
end
