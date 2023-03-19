include "cprime.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "cpc.mm"
include "co.mm"
include "cc0.mm"
include "wne.mm"
include "pcelnn.mm"
include "cn0.mm"
include "wb.mm"
include "pccl.mm"
include "nnne0.mm"
include "wceq.mm"
include "wo.mm"
include "elnn0.mm"
include "biimpi.mm"
include "ord.mm"
include "necon1ad.mm"
include "impbid2.mm"
include "syl.mm"
include "bitr3d.mm"
include "necon2bbid.mm"

theorem pceq0
  let cP: class P
  let cN: class N


  assert |- ( ( P e. Prime /\ N e. NN ) -> ( ( P pCnt N ) = 0 <-> -. P || N ) )

  proof
    cP
    cprime
    wcel
    cN
    cn
    wcel
    wa
    #
    cP
    cN
    cdvds
    wbr
    #
    cP
    cN
    cpc
    co
    #
    cc0
    @0
    @2
    cn
    wcel
    #
    @1
    @2
    cc0
    wne
    #
    cP
    cN
    pcelnn
    @0
    @2
    cn0
    wcel
    #
    @3
    @4
    wb
    cP
    cN
    pccl
    @5
    @3
    @4
    @2
    nnne0
    @5
    @3
    @2
    cc0
    @5
    @3
    @2
    cc0
    wceq
    #
    @5
    @3
    @6
    wo
    @2
    elnn0
    biimpi
    ord
    necon1ad
    impbid2
    syl
    bitr3d
    necon2bbid
end
