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
include "cprod.mm"
include "biid.mm"
include "nfcri.mm"
include "nfcv.mm"
include "nfif.mm"
include "weq.mm"
include "eleq1.mm"
include "ifbieq1d.mm"
include "cbvmpt.mm"
include "seqeq3.mm"
include "ax-mp.mm"
include "breq1i.mm"
include "anbi2i.mm"
include "exbii.mm"
include "rexbii.mm"
include "3anbi123i.mm"
include "cbvcsb.mm"
include "mpteq2i.mm"
include "fveq1i.mm"
include "eqeq2i.mm"
include "orbi12i.mm"
include "iotabii.mm"
include "df-prod.mm"
include "3eqtr4i.mm"

theorem cbvprod
  let cA: class A
  let cB: class B
  let cC: class C
  let vj: setvar j
  let vk: setvar k
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  assume cbvprod.1: |- ( j = k -> B = C )
  assume cbvprod.2: |- F/_ k A
  assume cbvprod.3: |- F/_ j A
  assume cbvprod.4: |- F/_ k B
  assume cbvprod.5: |- F/_ j C

  disjoint j k
  disjoint f j
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint A f
  disjoint A m
  disjoint A n
  disjoint A x
  disjoint A y
  disjoint B f
  disjoint B m
  disjoint B n
  disjoint B x
  disjoint B y
  disjoint C f
  disjoint C m
  disjoint C n
  disjoint C x
  disjoint C y
  assert |- prod_ j e. A B = prod_ k e. A C

  proof
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
    vj
    cz
    vj
    cv
    #
    cA
    wcel
    #
    cB
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
    @3
    cli
    wbr
    #
    wa
    #
    vy
    wex
    #
    vn
    @1
    wrex
    #
    cmul
    @8
    @0
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
    @0
    cfz
    co
    cA
    vf
    cv
    #
    wf1o
    #
    @16
    @0
    cmul
    vn
    cn
    vj
    @9
    @20
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
    @4
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
    @9
    cseq
    #
    @3
    cli
    wbr
    #
    wa
    #
    vy
    wex
    #
    vn
    @1
    wrex
    #
    cmul
    @35
    @0
    cseq
    #
    @16
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
    @16
    @0
    cmul
    vn
    cn
    vk
    @22
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
    cprod
    cA
    cC
    vk
    cprod
    @31
    @53
    vx
    @19
    @44
    @30
    @52
    @18
    @43
    vm
    cz
    @2
    @2
    @14
    @40
    @17
    @42
    @2
    biid
    @13
    @39
    vn
    @1
    @12
    @38
    vy
    @11
    @37
    @4
    @10
    @36
    @3
    cli
    @8
    @35
    wceq
    #
    @10
    @36
    wceq
    vj
    vk
    cz
    @7
    @34
    @6
    vk
    cB
    c1
    vk
    vj
    cA
    cbvprod.2
    nfcri
    cbvprod.4
    vk
    c1
    nfcv
    nfif
    @33
    vj
    cC
    c1
    vj
    vk
    cA
    cbvprod.3
    nfcri
    cbvprod.5
    vj
    c1
    nfcv
    nfif
    vj
    vk
    weq
    @6
    @33
    cB
    cC
    c1
    @5
    @32
    cA
    eleq1
    cbvprod.1
    ifbieq1d
    cbvmpt
    #
    cmul
    @8
    @35
    @9
    seqeq3
    ax-mp
    breq1i
    anbi2i
    exbii
    rexbii
    @15
    @41
    @16
    cli
    @54
    @15
    @41
    wceq
    @55
    cmul
    @8
    @35
    @0
    seqeq3
    ax-mp
    breq1i
    3anbi123i
    rexbii
    @29
    @51
    vm
    cn
    @28
    @50
    vf
    @27
    @49
    @21
    @26
    @48
    @16
    @0
    @25
    @47
    @24
    @46
    wceq
    @25
    @47
    wceq
    vn
    cn
    @23
    @45
    vj
    vk
    @22
    cB
    cC
    cbvprod.4
    cbvprod.5
    cbvprod.1
    cbvcsb
    mpteq2i
    cmul
    @24
    @46
    c1
    seqeq3
    ax-mp
    fveq1i
    eqeq2i
    anbi2i
    exbii
    rexbii
    orbi12i
    iotabii
    vx
    vy
    cA
    cB
    vf
    vj
    vm
    vn
    df-prod
    vx
    vy
    cA
    cC
    vf
    vk
    vm
    vn
    df-prod
    3eqtr4i
end
