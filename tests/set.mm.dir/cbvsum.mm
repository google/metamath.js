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
include "csu.mm"
include "wtru.mm"
include "cbvcsb.mm"
include "a1i.mm"
include "ifeq1d.mm"
include "mpteq2dv.mm"
include "seqeq3d.mm"
include "trud.mm"
include "breq1i.mm"
include "anbi2i.mm"
include "rexbii.mm"
include "fveq1i.mm"
include "eqeq2i.mm"
include "exbii.mm"
include "orbi12i.mm"
include "iotabii.mm"
include "df-sum.mm"
include "3eqtr4i.mm"

theorem cbvsum
  let cA: class A
  let cB: class B
  let cC: class C
  let vj: setvar j
  let vk: setvar k
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  assume cbvsum.1: |- ( j = k -> B = C )
  assume cbvsum.2: |- F/_ k A
  assume cbvsum.3: |- F/_ j A
  assume cbvsum.4: |- F/_ k B
  assume cbvsum.5: |- F/_ j C

  disjoint j k
  disjoint f j
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint m n
  disjoint m x
  disjoint n x
  disjoint A f
  disjoint A m
  disjoint A n
  disjoint A x
  disjoint B f
  disjoint B m
  disjoint B n
  disjoint B x
  disjoint C f
  disjoint C m
  disjoint C n
  disjoint C x
  assert |- sum_ j e. A B = sum_ k e. A C

  proof
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
    vj
    @2
    cB
    csb
    #
    cc0
    cif
    #
    cmpt
    #
    @0
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
    @0
    cfz
    co
    cA
    vf
    cv
    #
    wf1o
    #
    @8
    @0
    caddc
    vn
    cn
    vj
    @2
    @12
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
    @1
    caddc
    vn
    cz
    @3
    vk
    @2
    cC
    csb
    #
    cc0
    cif
    #
    cmpt
    #
    @0
    cseq
    #
    @8
    cli
    wbr
    #
    wa
    #
    vm
    cz
    wrex
    #
    @13
    @8
    @0
    caddc
    vn
    cn
    vk
    @14
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
    vj
    csu
    cA
    cC
    vk
    csu
    @23
    @39
    vx
    @11
    @30
    @22
    @38
    @10
    @29
    vm
    cz
    @9
    @28
    @1
    @7
    @27
    @8
    cli
    @7
    @27
    wceq
    wtru
    @6
    @26
    caddc
    @0
    wtru
    vn
    cz
    @5
    @25
    wtru
    @3
    @4
    @24
    cc0
    @4
    @24
    wceq
    wtru
    vj
    vk
    @2
    cB
    cC
    cbvsum.4
    cbvsum.5
    cbvsum.1
    cbvcsb
    a1i
    ifeq1d
    mpteq2dv
    seqeq3d
    trud
    breq1i
    anbi2i
    rexbii
    @21
    @37
    vm
    cn
    @20
    @36
    vf
    @19
    @35
    @13
    @18
    @34
    @8
    @0
    @17
    @33
    @17
    @33
    wceq
    wtru
    @16
    @32
    caddc
    c1
    wtru
    vn
    cn
    @15
    @31
    @15
    @31
    wceq
    wtru
    vj
    vk
    @14
    cB
    cC
    cbvsum.4
    cbvsum.5
    cbvsum.1
    cbvcsb
    a1i
    mpteq2dv
    seqeq3d
    trud
    fveq1i
    eqeq2i
    anbi2i
    exbii
    rexbii
    orbi12i
    iotabii
    vx
    cA
    cB
    vf
    vj
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
    3eqtr4i
end
