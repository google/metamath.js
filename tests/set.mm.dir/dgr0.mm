include "c0p.mm"
include "cdgr.mm"
include "cfv.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "df-0p.mm"
include "fveq2i.mm"
include "wcel.mm"
include "wceq.mm"
include "0cn.mm"
include "0dgr.mm"
include "ax-mp.mm"
include "eqtri.mm"

theorem dgr0
  let vk: setvar k
  let vz: setvar z
  let cA: class A
  let cF: class F
  let cN: class N
  let cS: class S


  assert |- ( deg ` 0p ) = 0

  proof
    c0p
    cdgr
    cfv
    cc
    cc0
    csn
    cxp
    #
    cdgr
    cfv
    #
    cc0
    c0p
    @0
    cdgr
    df-0p
    fveq2i
    cc0
    cc
    wcel
    @1
    cc0
    wceq
    0cn
    cc0
    0dgr
    ax-mp
    eqtri
end
