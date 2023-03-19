include "cumgr.mm"
include "wcel.mm"
include "cdm.mm"
include "wa.mm"
include "cfv.mm"
include "wss.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "cpr.mm"
include "wi.mm"
include "cuhgr.mm"
include "umgruhgr.mm"
include "uhgrss.mm"
include "sylan.mm"
include "umgredg2.mm"
include "sseq1.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "wne.mm"
include "w3a.mm"
include "eqid.mm"
include "hashprdifel.mm"
include "wb.mm"
include "prssg.mm"
include "3adant3.mm"
include "biimprd.mm"
include "syl.mm"
include "impcom.mm"
include "syl6bi.mm"
include "com12.mm"
include "syl2anc.mm"

theorem umgredgprv
  let cE: class E
  let cG: class G
  let cM: class M
  let cN: class N
  let cV: class V
  let cX: class X
  assume umgrnloopv.e: |- E = ( iEdg ` G )
  assume umgredgprv.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. UMGraph /\ X e. dom E ) -> ( ( E ` X ) = { M , N } -> ( M e. V /\ N e. V ) ) )

  proof
    cG
    cumgr
    wcel
    #
    cX
    cE
    cdm
    wcel
    #
    wa
    cX
    cE
    cfv
    #
    cV
    wss
    #
    @2
    chash
    cfv
    #
    c2
    wceq
    #
    @2
    cM
    cN
    cpr
    #
    wceq
    #
    cM
    cV
    wcel
    cN
    cV
    wcel
    wa
    #
    wi
    @0
    cG
    cuhgr
    wcel
    @1
    @3
    cG
    umgruhgr
    cE
    cX
    cG
    cV
    umgredgprv.v
    umgrnloopv.e
    uhgrss
    sylan
    cE
    cG
    cV
    cX
    umgredgprv.v
    umgrnloopv.e
    umgredg2
    @7
    @3
    @5
    wa
    #
    @8
    @7
    @9
    @6
    cV
    wss
    #
    @6
    chash
    cfv
    #
    c2
    wceq
    #
    wa
    @8
    @7
    @3
    @10
    @5
    @12
    @2
    @6
    cV
    sseq1
    @7
    @4
    @11
    c2
    @2
    @6
    chash
    fveq2
    eqeq1d
    anbi12d
    @12
    @10
    @8
    @12
    cM
    @6
    wcel
    #
    cN
    @6
    wcel
    #
    cM
    cN
    wne
    #
    w3a
    #
    @10
    @8
    wi
    cM
    cN
    @6
    @6
    eqid
    hashprdifel
    @16
    @8
    @10
    @13
    @14
    @8
    @10
    wb
    @15
    cM
    cN
    cV
    @6
    @6
    prssg
    3adant3
    biimprd
    syl
    impcom
    syl6bi
    com12
    syl2anc
end
