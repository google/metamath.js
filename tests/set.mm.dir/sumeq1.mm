include "wceq.mm"
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
include "wex.mm"
include "wo.mm"
include "cio.mm"
include "csu.mm"
include "sseq1.mm"
include "simpl.mm"
include "eleq2d.mm"
include "ifbid.mm"
include "mpteq2dva.mm"
include "seqeq3d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "f1oeq3.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "orbi12d.mm"
include "iotabidv.mm"
include "df-sum.mm"
include "3eqtr4g.mm"

theorem sumeq1
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x


  assert |- ( A = B -> sum_ k e. A C = sum_ k e. B C )

  proof
    cA
    cB
    wceq
    #
    cA
    vm
    cv
    #
    cuz
    cfv
    #
    wss
    #
    caddc
    vn
    cz
    vn
    cv
    #
    cA
    wcel
    #
    vk
    @4
    cC
    csb
    #
    cc0
    cif
    #
    cmpt
    #
    @1
    cseq
    #
    vx
    cv
    #
    cli
    wbr
    #
    wa
    #
    vm
    cz
    wrex
    #
    c1
    @1
    cfz
    co
    #
    cA
    vf
    cv
    #
    wf1o
    #
    @10
    @1
    caddc
    vn
    cn
    vk
    @4
    @15
    cfv
    cC
    csb
    cmpt
    c1
    cseq
    cfv
    wceq
    #
    wa
    #
    vf
    wex
    #
    vm
    cn
    wrex
    #
    wo
    #
    vx
    cio
    cB
    @2
    wss
    #
    caddc
    vn
    cz
    @4
    cB
    wcel
    #
    @6
    cc0
    cif
    #
    cmpt
    #
    @1
    cseq
    #
    @10
    cli
    wbr
    #
    wa
    #
    vm
    cz
    wrex
    #
    @14
    cB
    @15
    wf1o
    #
    @17
    wa
    #
    vf
    wex
    #
    vm
    cn
    wrex
    #
    wo
    #
    vx
    cio
    cA
    cC
    vk
    csu
    cB
    cC
    vk
    csu
    @0
    @21
    @34
    vx
    @0
    @13
    @29
    @20
    @33
    @0
    @12
    @28
    vm
    cz
    @0
    @3
    @22
    @11
    @27
    cA
    cB
    @2
    sseq1
    @0
    @9
    @26
    @10
    cli
    @0
    @8
    @25
    caddc
    @1
    @0
    vn
    cz
    @7
    @24
    @0
    @4
    cz
    wcel
    #
    wa
    #
    @5
    @23
    @6
    cc0
    @36
    cA
    cB
    @4
    @0
    @35
    simpl
    eleq2d
    ifbid
    mpteq2dva
    seqeq3d
    breq1d
    anbi12d
    rexbidv
    @0
    @19
    @32
    vm
    cn
    @0
    @18
    @31
    vf
    @0
    @16
    @30
    @17
    cA
    cB
    @14
    @15
    f1oeq3
    anbi1d
    exbidv
    rexbidv
    orbi12d
    iotabidv
    vx
    cA
    cC
    vf
    vk
    vm
    vn
    df-sum
    vx
    cB
    cC
    vf
    vk
    vm
    vn
    df-sum
    3eqtr4g
end
