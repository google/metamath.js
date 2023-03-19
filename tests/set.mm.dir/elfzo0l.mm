include "cn.mm"
include "wcel.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wceq.mm"
include "c1.mm"
include "wo.mm"
include "cn0.mm"
include "clt.mm"
include "wbr.mm"
include "elfzo0.mm"
include "simp2bi.mm"
include "csn.mm"
include "cun.mm"
include "fzo0sn0fzo1.mm"
include "eleq2d.mm"
include "elun.mm"
include "elsni.mm"
include "orim1i.mm"
include "sylbi.mm"
include "syl6bi.mm"
include "mpcom.mm"

theorem elfzo0l
  let cK: class K
  let cN: class N


  assert |- ( K e. ( 0 ..^ N ) -> ( K = 0 \/ K e. ( 1 ..^ N ) ) )

  proof
    cN
    cn
    wcel
    #
    cK
    cc0
    cN
    cfzo
    co
    #
    wcel
    #
    cK
    cc0
    wceq
    #
    cK
    c1
    cN
    cfzo
    co
    #
    wcel
    #
    wo
    #
    @2
    cK
    cn0
    wcel
    @0
    cK
    cN
    clt
    wbr
    cK
    cN
    elfzo0
    simp2bi
    @0
    @2
    cK
    cc0
    csn
    #
    @4
    cun
    #
    wcel
    #
    @6
    @0
    @1
    @8
    cK
    cN
    fzo0sn0fzo1
    eleq2d
    @9
    cK
    @7
    wcel
    #
    @5
    wo
    @6
    cK
    @7
    @4
    elun
    @10
    @3
    @5
    cK
    cc0
    elsni
    orim1i
    sylbi
    syl6bi
    mpcom
end
