include "wcel.mm"
include "c0.mm"
include "cpths.mm"
include "cfv.mm"
include "wbr.mm"
include "cc0.mm"
include "chash.mm"
include "wceq.mm"
include "wa.mm"
include "cfz.mm"
include "co.mm"
include "cvtx.mm"
include "wf.mm"
include "ccycls.mm"
include "eqid.mm"
include "0pth.mm"
include "anbi1d.mm"
include "iscycl.mm"
include "hash0.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "biantru.mm"
include "3bitr4g.mm"

theorem 0cycl
  let cP: class P
  let cG: class G
  let cW: class W


  assert |- ( G e. W -> ( (/) ( Cycles ` G ) P <-> P : ( 0 ... 0 ) --> ( Vtx ` G ) ) )

  proof
    cG
    cW
    wcel
    #
    c0
    cP
    cG
    cpths
    cfv
    wbr
    #
    cc0
    cP
    cfv
    c0
    chash
    cfv
    #
    cP
    cfv
    wceq
    #
    wa
    cc0
    cc0
    cfz
    co
    cG
    cvtx
    cfv
    #
    cP
    wf
    #
    @3
    wa
    c0
    cP
    cG
    ccycls
    cfv
    wbr
    @5
    @0
    @1
    @5
    @3
    cP
    cG
    @4
    cW
    @4
    eqid
    0pth
    anbi1d
    cP
    c0
    cG
    iscycl
    @3
    @5
    cc0
    @2
    cP
    @2
    cc0
    hash0
    eqcomi
    fveq2i
    biantru
    3bitr4g
end
