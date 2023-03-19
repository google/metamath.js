include "cumgr.mm"
include "wcel.mm"
include "cpr.mm"
include "wa.mm"
include "cvtx.mm"
include "cfv.mm"
include "cpw.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "cedg.mm"
include "eleq2i.mm"
include "edgumgr.mm"
include "sylan2b.mm"
include "wne.mm"
include "w3a.mm"
include "wi.mm"
include "eqid.mm"
include "hashprdifel.mm"
include "eqcomi.mm"
include "pweqi.mm"
include "prelpw.mm"
include "biimprd.mm"
include "syl5bi.mm"
include "3adant3.mm"
include "syl.mm"
include "impcom.mm"

theorem umgrpredgv
  let cE: class E
  let cG: class G
  let cM: class M
  let cN: class N
  let cV: class V
  let cC: class C
  let vx: setvar x
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume upgredg.v: |- V = ( Vtx ` G )
  assume upgredg.e: |- E = ( Edg ` G )


  assert |- ( ( G e. UMGraph /\ { M , N } e. E ) -> ( M e. V /\ N e. V ) )

  proof
    cG
    cumgr
    wcel
    #
    cM
    cN
    cpr
    #
    cE
    wcel
    #
    wa
    @1
    cG
    cvtx
    cfv
    #
    cpw
    #
    wcel
    #
    @1
    chash
    cfv
    c2
    wceq
    #
    wa
    #
    cM
    cV
    wcel
    cN
    cV
    wcel
    wa
    #
    @2
    @0
    @1
    cG
    cedg
    cfv
    #
    wcel
    @7
    cE
    @9
    @1
    upgredg.e
    eleq2i
    @1
    cG
    edgumgr
    sylan2b
    @6
    @5
    @8
    @6
    cM
    @1
    wcel
    #
    cN
    @1
    wcel
    #
    cM
    cN
    wne
    #
    w3a
    @5
    @8
    wi
    #
    cM
    cN
    @1
    @1
    eqid
    hashprdifel
    @10
    @11
    @13
    @12
    @5
    @1
    cV
    cpw
    #
    wcel
    #
    @10
    @11
    wa
    #
    @8
    @4
    @14
    @1
    @3
    cV
    cV
    @3
    upgredg.v
    eqcomi
    pweqi
    eleq2i
    @16
    @8
    @15
    cM
    cN
    cV
    @1
    @1
    prelpw
    biimprd
    syl5bi
    3adant3
    syl
    impcom
    syl
end
