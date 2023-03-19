include "cfusgr.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "cnbgr.mm"
include "co.mm"
include "wnel.mm"
include "w3a.mm"
include "chash.mm"
include "cfv.mm"
include "cpr.mm"
include "cdif.mm"
include "c2.mm"
include "cmin.mm"
include "cle.mm"
include "cvv.mm"
include "wss.mm"
include "wbr.mm"
include "cvtx.mm"
include "fvexi.mm"
include "difexg.mm"
include "mp1i.mm"
include "simpr3.mm"
include "nbgrssvwo2.mm"
include "syl.mm"
include "hashss.mm"
include "syl2anc.mm"
include "cfn.mm"
include "wceq.mm"
include "fusgrvtxfi.mm"
include "ad2antrr.mm"
include "simpr1.mm"
include "simplr.mm"
include "simpr2.mm"
include "hashdifpr.mm"
include "syl13anc.mm"
include "breqtrd.mm"

theorem nbfusgrlevtxm2
  let cU: class U
  let cG: class G
  let cM: class M
  let cV: class V
  assume hashnbusgrnn0.v: |- V = ( Vtx ` G )


  assert |- ( ( ( G e. FinUSGraph /\ U e. V ) /\ ( M e. V /\ M =/= U /\ M e/ ( G NeighbVtx U ) ) ) -> ( # ` ( G NeighbVtx U ) ) <_ ( ( # ` V ) - 2 ) )

  proof
    cG
    cfusgr
    wcel
    #
    cU
    cV
    wcel
    #
    wa
    #
    cM
    cV
    wcel
    #
    cM
    cU
    wne
    #
    cM
    cG
    cU
    cnbgr
    co
    #
    wnel
    #
    w3a
    #
    wa
    #
    @5
    chash
    cfv
    #
    cV
    cM
    cU
    cpr
    #
    cdif
    #
    chash
    cfv
    #
    cV
    chash
    cfv
    c2
    cmin
    co
    #
    cle
    @8
    @11
    cvv
    wcel
    #
    @5
    @11
    wss
    #
    @9
    @12
    cle
    wbr
    cV
    cvv
    wcel
    @14
    @8
    cV
    cG
    cvtx
    hashnbusgrnn0.v
    fvexi
    cV
    @10
    cvv
    difexg
    mp1i
    @8
    @6
    @15
    @2
    @3
    @4
    @6
    simpr3
    cG
    cM
    cV
    cU
    hashnbusgrnn0.v
    nbgrssvwo2
    syl
    @11
    @5
    cvv
    hashss
    syl2anc
    @8
    cV
    cfn
    wcel
    #
    @3
    @1
    @4
    @12
    @13
    wceq
    @0
    @16
    @1
    @7
    cG
    cV
    hashnbusgrnn0.v
    fusgrvtxfi
    ad2antrr
    @2
    @3
    @4
    @6
    simpr1
    @0
    @1
    @7
    simplr
    @2
    @3
    @4
    @6
    simpr2
    cV
    cM
    cU
    hashdifpr
    syl13anc
    breqtrd
end
