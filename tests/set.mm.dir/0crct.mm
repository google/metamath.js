include "wcel.mm"
include "c0.mm"
include "ctrls.mm"
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
include "ccrcts.mm"
include "eqid.mm"
include "0trl.mm"
include "anbi1d.mm"
include "iscrct.mm"
include "hash0.mm"
include "eqcomi.mm"
include "a1i.mm"
include "fveq2d.mm"
include "pm4.71i.mm"
include "3bitr4g.mm"

theorem 0crct
  let cP: class P
  let cG: class G
  let cW: class W


  assert |- ( G e. W -> ( (/) ( Circuits ` G ) P <-> P : ( 0 ... 0 ) --> ( Vtx ` G ) ) )

  proof
    cG
    cW
    wcel
    #
    c0
    cP
    cG
    ctrls
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
    ccrcts
    cfv
    wbr
    @5
    @0
    @1
    @5
    @3
    cP
    cW
    cG
    @4
    @4
    eqid
    0trl
    anbi1d
    cP
    c0
    cG
    iscrct
    @5
    @3
    @5
    cc0
    @2
    cP
    cc0
    @2
    wceq
    @5
    @2
    cc0
    hash0
    eqcomi
    a1i
    fveq2d
    pm4.71i
    3bitr4g
end
