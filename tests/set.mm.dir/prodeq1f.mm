include "wceq.mm"
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
include "wo.mm"
include "cio.mm"
include "cprod.mm"
include "sseq1.mm"
include "nfeq.mm"
include "eleq2.mm"
include "ifbid.mm"
include "adantr.mm"
include "mpteq2da.mm"
include "seqeq3d.mm"
include "breq1d.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "rexbidv.mm"
include "3anbi123d.mm"
include "f1oeq3.mm"
include "anbi1d.mm"
include "orbi12d.mm"
include "iotabidv.mm"
include "df-prod.mm"
include "3eqtr4g.mm"

theorem prodeq1f
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  assume prodeq1f.1: |- F/_ k A
  assume prodeq1f.2: |- F/_ k B


  assert |- ( A = B -> prod_ k e. A C = prod_ k e. B C )

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
    vy
    cv
    #
    cc0
    wne
    #
    cmul
    vk
    cz
    vk
    cv
    #
    cA
    wcel
    #
    cC
    c1
    cif
    #
    cmpt
    #
    vn
    cv
    #
    cseq
    #
    @4
    cli
    wbr
    #
    wa
    #
    vy
    wex
    #
    vn
    @2
    wrex
    #
    cmul
    @9
    @1
    cseq
    #
    vx
    cv
    #
    cli
    wbr
    #
    w3a
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
    @17
    @1
    cmul
    vn
    cn
    vk
    @10
    @22
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
    @5
    cmul
    vk
    cz
    @6
    cB
    wcel
    #
    cC
    c1
    cif
    #
    cmpt
    #
    @10
    cseq
    #
    @4
    cli
    wbr
    #
    wa
    #
    vy
    wex
    #
    vn
    @2
    wrex
    #
    cmul
    @32
    @1
    cseq
    #
    @17
    cli
    wbr
    #
    w3a
    #
    vm
    cz
    wrex
    #
    @21
    cB
    @22
    wf1o
    #
    @24
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
    cprod
    cB
    cC
    vk
    cprod
    @0
    @28
    @46
    vx
    @0
    @20
    @41
    @27
    @45
    @0
    @19
    @40
    vm
    cz
    @0
    @3
    @29
    @15
    @37
    @18
    @39
    cA
    cB
    @2
    sseq1
    @0
    @14
    @36
    vn
    @2
    @0
    @13
    @35
    vy
    @0
    @12
    @34
    @5
    @0
    @11
    @33
    @4
    cli
    @0
    @9
    @32
    cmul
    @10
    @0
    vk
    cz
    @8
    @31
    vk
    cA
    cB
    prodeq1f.1
    prodeq1f.2
    nfeq
    @0
    @8
    @31
    wceq
    @6
    cz
    wcel
    @0
    @7
    @30
    cC
    c1
    cA
    cB
    @6
    eleq2
    ifbid
    adantr
    mpteq2da
    #
    seqeq3d
    breq1d
    anbi2d
    exbidv
    rexbidv
    @0
    @16
    @38
    @17
    cli
    @0
    @9
    @32
    cmul
    @1
    @47
    seqeq3d
    breq1d
    3anbi123d
    rexbidv
    @0
    @26
    @44
    vm
    cn
    @0
    @25
    @43
    vf
    @0
    @23
    @42
    @24
    cA
    cB
    @21
    @22
    f1oeq3
    anbi1d
    exbidv
    rexbidv
    orbi12d
    iotabidv
    vx
    vy
    cA
    cC
    vf
    vk
    vm
    vn
    df-prod
    vx
    vy
    cB
    cC
    vf
    vk
    vm
    vn
    df-prod
    3eqtr4g
end
