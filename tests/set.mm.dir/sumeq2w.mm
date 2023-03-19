include "wceq.mm"
include "wal.mm"
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
include "csbeq2.mm"
include "ifeq1d.mm"
include "mpteq2dv.mm"
include "seqeq3d.mm"
include "breq1d.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "fveq1d.mm"
include "eqeq2d.mm"
include "exbidv.mm"
include "orbi12d.mm"
include "iotabidv.mm"
include "df-sum.mm"
include "3eqtr4g.mm"

theorem sumeq2w
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x


  assert |- ( A. k B = C -> sum_ k e. A B = sum_ k e. A C )

  proof
    cB
    cC
    wceq
    vk
    wal
    #
    cA
    vm
    cv
    #
    cuz
    cfv
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
    @3
    cB
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
    cA
    vf
    cv
    #
    wf1o
    #
    @9
    @1
    caddc
    vn
    cn
    vk
    @3
    @13
    cfv
    #
    cB
    csb
    #
    cmpt
    #
    c1
    cseq
    #
    cfv
    #
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
    @2
    caddc
    vn
    cz
    @4
    vk
    @3
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
    @9
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
    @9
    @1
    caddc
    vn
    cn
    vk
    @15
    cC
    csb
    #
    cmpt
    #
    c1
    cseq
    #
    cfv
    #
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
    cA
    cB
    vk
    csu
    cA
    cC
    vk
    csu
    @0
    @24
    @40
    vx
    @0
    @12
    @31
    @23
    @39
    @0
    @11
    @30
    vm
    cz
    @0
    @10
    @29
    @2
    @0
    @8
    @28
    @9
    cli
    @0
    @7
    @27
    caddc
    @1
    @0
    vn
    cz
    @6
    @26
    @0
    @4
    @5
    @25
    cc0
    vk
    @3
    cB
    cC
    csbeq2
    ifeq1d
    mpteq2dv
    seqeq3d
    breq1d
    anbi2d
    rexbidv
    @0
    @22
    @38
    vm
    cn
    @0
    @21
    @37
    vf
    @0
    @20
    @36
    @14
    @0
    @19
    @35
    @9
    @0
    @1
    @18
    @34
    @0
    @17
    @33
    caddc
    c1
    @0
    vn
    cn
    @16
    @32
    vk
    @15
    cB
    cC
    csbeq2
    mpteq2dv
    seqeq3d
    fveq1d
    eqeq2d
    anbi2d
    exbidv
    rexbidv
    orbi12d
    iotabidv
    vx
    cA
    cB
    vf
    vk
    vm
    vn
    df-sum
    vx
    cA
    cC
    vf
    vk
    vm
    vn
    df-sum
    3eqtr4g
end
