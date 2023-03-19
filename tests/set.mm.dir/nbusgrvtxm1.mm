include "cnbgr.mm"
include "co.mm"
include "wcel.mm"
include "cfusgr.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "wceq.mm"
include "wne.mm"
include "wi.mm"
include "ax-1.mm"
include "2a1d.mm"
include "wn.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "wnel.mm"
include "simpr.mm"
include "adantr.mm"
include "simprl.mm"
include "adantl.mm"
include "df-nel.mm"
include "biimpri.mm"
include "nbfusgrlevtxm2.mm"
include "syl13anc.mm"
include "wb.mm"
include "breq1.mm"
include "cfn.mm"
include "cn0.mm"
include "fusgrvtxfi.mm"
include "hashcl.mm"
include "cr.mm"
include "nn0re.mm"
include "clt.mm"
include "1red.mm"
include "2re.mm"
include "a1i.mm"
include "id.mm"
include "1lt2.mm"
include "ltsub2dd.mm"
include "resubcld.mm"
include "peano2rem.mm"
include "ltnled.mm"
include "mpbid.mm"
include "syl.mm"
include "3syl.mm"
include "pm2.21d.mm"
include "ad3antlr.mm"
include "sylbid.mm"
include "ex.mm"
include "mpid.mm"
include "com23.mm"
include "pm2.61i.mm"

theorem nbusgrvtxm1
  let cU: class U
  let cG: class G
  let cM: class M
  let cV: class V
  assume hashnbusgrnn0.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. FinUSGraph /\ U e. V ) -> ( ( # ` ( G NeighbVtx U ) ) = ( ( # ` V ) - 1 ) -> ( ( M e. V /\ M =/= U ) -> M e. ( G NeighbVtx U ) ) ) )

  proof
    cM
    cG
    cU
    cnbgr
    co
    #
    wcel
    #
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
    @0
    chash
    cfv
    #
    cV
    chash
    cfv
    #
    c1
    cmin
    co
    #
    wceq
    #
    cM
    cV
    wcel
    #
    cM
    cU
    wne
    #
    wa
    #
    @1
    wi
    #
    wi
    #
    wi
    @1
    @12
    @4
    @8
    @1
    @11
    ax-1
    2a1d
    @1
    wn
    #
    @4
    @13
    @14
    @4
    wa
    #
    @11
    @8
    @1
    @15
    @11
    @8
    @1
    wi
    @15
    @11
    wa
    #
    @8
    @5
    @6
    c2
    cmin
    co
    #
    cle
    wbr
    #
    @1
    @16
    @4
    @9
    @10
    cM
    @0
    wnel
    #
    @18
    @15
    @4
    @11
    @14
    @4
    simpr
    adantr
    @15
    @9
    @10
    simprl
    @11
    @10
    @15
    @9
    @10
    simpr
    adantl
    @15
    @19
    @11
    @14
    @19
    @4
    @19
    @14
    cM
    @0
    df-nel
    biimpri
    adantr
    adantr
    cU
    cG
    cM
    cV
    hashnbusgrnn0.v
    nbfusgrlevtxm2
    syl13anc
    @16
    @8
    @18
    @1
    wi
    @16
    @8
    wa
    @18
    @7
    @17
    cle
    wbr
    #
    @1
    @8
    @18
    @20
    wb
    @16
    @5
    @7
    @17
    cle
    breq1
    adantl
    @4
    @20
    @1
    wi
    #
    @14
    @11
    @8
    @2
    @21
    @3
    @2
    @20
    @1
    @2
    cV
    cfn
    wcel
    @6
    cn0
    wcel
    #
    @20
    wn
    #
    cG
    cV
    hashnbusgrnn0.v
    fusgrvtxfi
    cV
    hashcl
    @22
    @6
    cr
    wcel
    #
    @23
    @6
    nn0re
    @24
    @17
    @7
    clt
    wbr
    @23
    @24
    c1
    c2
    @6
    @24
    1red
    c2
    cr
    wcel
    @24
    2re
    a1i
    #
    @24
    id
    #
    c1
    c2
    clt
    wbr
    @24
    1lt2
    a1i
    ltsub2dd
    @24
    @17
    @7
    @24
    @6
    c2
    @26
    @25
    resubcld
    @6
    peano2rem
    ltnled
    mpbid
    syl
    3syl
    pm2.21d
    adantr
    ad3antlr
    sylbid
    ex
    mpid
    ex
    com23
    ex
    pm2.61i
end
