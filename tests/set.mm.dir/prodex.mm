include "cprod.mm"
include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "cc0.mm"
include "wne.mm"
include "cmul.mm"
include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "cif.mm"
include "cmpt.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "w3a.mm"
include "cfz.mm"
include "co.mm"
include "wf1o.mm"
include "cn.mm"
include "csb.mm"
include "wceq.mm"
include "wo.mm"
include "cio.mm"
include "cvv.mm"
include "df-prod.mm"
include "iotaex.mm"
include "eqeltri.mm"

theorem prodex
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y


  assert |- prod_ k e. A B e. _V

  proof
    cA
    cB
    vk
    cprod
    cA
    vm
    cv
    #
    cuz
    cfv
    #
    wss
    vy
    cv
    #
    cc0
    wne
    cmul
    vk
    cz
    vk
    cv
    cA
    wcel
    cB
    c1
    cif
    cmpt
    #
    vn
    cv
    #
    cseq
    @2
    cli
    wbr
    wa
    vy
    wex
    vn
    @1
    wrex
    cmul
    @3
    @0
    cseq
    vx
    cv
    #
    cli
    wbr
    w3a
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
    @5
    @0
    cmul
    vn
    cn
    vk
    @4
    @6
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
    vy
    cA
    cB
    vf
    vk
    vm
    vn
    df-prod
    @7
    vx
    iotaex
    eqeltri
end
