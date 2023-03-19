include "cusgr.mm"
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
include "usgrss.mm"
include "usgredg2.mm"
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

theorem usgredgprvALT
  let cE: class E
  let cG: class G
  let cM: class M
  let cN: class N
  let cV: class V
  let cX: class X
  let vx: setvar x
  assume usgredg2.e: |- E = ( iEdg ` G )
  assume usgredgprv.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. USGraph /\ X e. dom E ) -> ( ( E ` X ) = { M , N } -> ( M e. V /\ N e. V ) ) )

  proof
    cG
    cusgr
    wcel
    cX
    cE
    cdm
    wcel
    wa
    cX
    cE
    cfv
    #
    cV
    wss
    #
    @0
    chash
    cfv
    #
    c2
    wceq
    #
    @0
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
    cE
    cG
    cV
    cX
    usgredg2.e
    usgredgprv.v
    usgrss
    cE
    cG
    cX
    usgredg2.e
    usgredg2
    @5
    @1
    @3
    wa
    #
    @6
    @5
    @7
    @4
    cV
    wss
    #
    @4
    chash
    cfv
    #
    c2
    wceq
    #
    wa
    @6
    @5
    @1
    @8
    @3
    @10
    @0
    @4
    cV
    sseq1
    @5
    @2
    @9
    c2
    @0
    @4
    chash
    fveq2
    eqeq1d
    anbi12d
    @10
    @8
    @6
    @10
    cM
    @4
    wcel
    #
    cN
    @4
    wcel
    #
    cM
    cN
    wne
    #
    w3a
    #
    @8
    @6
    wi
    cM
    cN
    @4
    @4
    eqid
    hashprdifel
    @14
    @6
    @8
    @11
    @12
    @6
    @8
    wb
    @13
    cM
    cN
    cV
    @4
    @4
    prssg
    3adant3
    biimprd
    syl
    impcom
    syl6bi
    com12
    syl2anc
end
