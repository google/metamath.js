include "csu.mm"
include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "caddc.mm"
include "cz.mm"
include "wcel.mm"
include "csb.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "wa.mm"
include "wrex.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wf1o.mm"
include "cn.mm"
include "wceq.mm"
include "wex.mm"
include "wo.mm"
include "cio.mm"
include "cvv.mm"
include "df-sum.mm"
include "iotaex.mm"
include "eqeltri.mm"

theorem sumex
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x


  assert |- sum_ k e. A B e. _V

  proof
    cA
    cB
    vk
    csu
    cA
    vm
    cv
    #
    cuz
    cfv
    wss
    caddc
    vn
    cz
    vn
    cv
    #
    cA
    wcel
    vk
    @1
    cB
    csb
    cc0
    cif
    cmpt
    @0
    cseq
    vx
    cv
    #
    cli
    wbr
    wa
    vm
    cz
    wrex
    c1
    @0
    cfz
    co
    cA
    vf
    cv
    #
    wf1o
    @2
    @0
    caddc
    vn
    cn
    vk
    @1
    @3
    cfv
    cB
    csb
    cmpt
    c1
    cseq
    cfv
    wceq
    wa
    vf
    wex
    vm
    cn
    wrex
    wo
    #
    vx
    cio
    cvv
    vx
    cA
    cB
    vf
    vk
    vm
    vn
    df-sum
    @4
    vx
    iotaex
    eqeltri
end
