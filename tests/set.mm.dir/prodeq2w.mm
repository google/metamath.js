include "wceq.mm"
include "wal.mm"
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
include "wral.mm"
include "eqid.mm"
include "ifeq1.mm"
include "alimi.mm"
include "alral.mm"
include "syl.mm"
include "mpteq12.mm"
include "sylancr.mm"
include "seqeq3d.mm"
include "breq1d.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "rexbidv.mm"
include "3anbi23d.mm"
include "csbeq2.mm"
include "mpteq2dv.mm"
include "fveq1d.mm"
include "eqeq2d.mm"
include "orbi12d.mm"
include "iotabidv.mm"
include "df-prod.mm"
include "3eqtr4g.mm"

theorem prodeq2w
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y

  disjoint A k
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint x y
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
  assert |- ( A. k B = C -> prod_ k e. A B = prod_ k e. A C )

  proof
    cB
    cC
    wceq
    #
    vk
    wal
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
    @5
    cli
    wbr
    #
    wa
    #
    vy
    wex
    #
    vn
    @3
    wrex
    #
    cmul
    @9
    @2
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
    @2
    cfz
    co
    cA
    vf
    cv
    #
    wf1o
    #
    @17
    @2
    cmul
    vn
    cn
    vk
    @10
    @21
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
    @4
    @6
    cmul
    vk
    cz
    @7
    cC
    c1
    cif
    #
    cmpt
    #
    @10
    cseq
    #
    @5
    cli
    wbr
    #
    wa
    #
    vy
    wex
    #
    vn
    @3
    wrex
    #
    cmul
    @34
    @2
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
    @22
    @17
    @2
    cmul
    vn
    cn
    vk
    @23
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
    cprod
    cA
    cC
    vk
    cprod
    @1
    @32
    @52
    vx
    @1
    @20
    @43
    @31
    @51
    @1
    @19
    @42
    vm
    cz
    @1
    @15
    @39
    @18
    @41
    @4
    @1
    @14
    @38
    vn
    @3
    @1
    @13
    @37
    vy
    @1
    @12
    @36
    @6
    @1
    @11
    @35
    @5
    cli
    @1
    @9
    @34
    cmul
    @10
    @1
    cz
    cz
    wceq
    @8
    @33
    wceq
    #
    vk
    cz
    wral
    #
    @9
    @34
    wceq
    cz
    eqid
    @1
    @53
    vk
    wal
    @54
    @0
    @53
    vk
    @7
    cB
    cC
    c1
    ifeq1
    alimi
    @53
    vk
    cz
    alral
    syl
    vk
    cz
    @8
    cz
    @33
    mpteq12
    sylancr
    #
    seqeq3d
    breq1d
    anbi2d
    exbidv
    rexbidv
    @1
    @16
    @40
    @17
    cli
    @1
    @9
    @34
    cmul
    @2
    @55
    seqeq3d
    breq1d
    3anbi23d
    rexbidv
    @1
    @30
    @50
    vm
    cn
    @1
    @29
    @49
    vf
    @1
    @28
    @48
    @22
    @1
    @27
    @47
    @17
    @1
    @2
    @26
    @46
    @1
    @25
    @45
    cmul
    c1
    @1
    vn
    cn
    @24
    @44
    vk
    @23
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
    vy
    cA
    cB
    vf
    vk
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
    3eqtr4g
end
