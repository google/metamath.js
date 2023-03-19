include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cuz.mm"
include "cima.mm"
include "cc0.mm"
include "csn.mm"
include "wceq.mm"
include "cc.mm"
include "cfz.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "wa.mm"
include "cn0.mm"
include "wrex.mm"
include "cmap.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "cun.mm"
include "plyssc.mm"
include "sseli.mm"
include "wss.mm"
include "elply2.mm"
include "simprbi.mm"
include "rexcom.mm"
include "sylib.mm"
include "syl.mm"
include "0cn.mm"
include "snssi.mm"
include "ax-mp.mm"
include "ssequn2.mm"
include "mpbi.mm"
include "oveq1i.mm"
include "rexeqi.mm"
include "reeanv.mm"
include "w3a.mm"
include "simp1l.mm"
include "simp1rl.mm"
include "simp1rr.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp3ll.mm"
include "simp3rl.mm"
include "simp3lr.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "sumeq2sdv.mm"
include "fveq2.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "cbvsumv.mm"
include "syl6eq.mm"
include "cbvmptv.mm"
include "simp3rr.mm"
include "coeeulem.mm"
include "3expia.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "ralrimivva.mm"
include "imaeq1.mm"
include "eqeq1d.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "mpteq2dv.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "fveq2d.mm"
include "imaeq2d.mm"
include "sumeq1d.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "reu4.mm"
include "sylanbrc.mm"

theorem coeeu
  let vz: setvar z
  let cS: class S
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let va: setvar a
  let vy: setvar y
  let cB: class B
  let vb: setvar b
  let vf: setvar f
  let vj: setvar j
  let vm: setvar m
  let vw: setvar w
  let vx: setvar x
  let wph: wff ph
  let cA: class A
  let cM: class M
  let cN: class N

  disjoint k z
  disjoint a n
  disjoint F a
  disjoint F n
  disjoint S a
  disjoint S n
  disjoint a k
  disjoint a z
  disjoint k n
  disjoint n z
  disjoint k y
  disjoint B k
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint a b
  disjoint a f
  disjoint a j
  disjoint a m
  disjoint a w
  disjoint b f
  disjoint b j
  disjoint b m
  disjoint b n
  disjoint b w
  disjoint F b
  disjoint f j
  disjoint f m
  disjoint f n
  disjoint f w
  disjoint F f
  disjoint j m
  disjoint j n
  disjoint j w
  disjoint F j
  disjoint m n
  disjoint m w
  disjoint F m
  disjoint n w
  disjoint F w
  disjoint k x
  disjoint k ph
  disjoint x y
  disjoint x z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint S b
  disjoint S j
  disjoint S m
  disjoint S w
  disjoint b k
  disjoint b z
  disjoint f k
  disjoint f z
  disjoint j k
  disjoint j z
  disjoint k m
  disjoint k w
  disjoint m z
  disjoint w z
  disjoint A k
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint M k
  disjoint M z
  disjoint N k
  disjoint N z
  assert |- ( F e. ( Poly ` S ) -> E! a e. ( CC ^m NN0 ) E. n e. NN0 ( ( a " ( ZZ>= ` ( n + 1 ) ) ) = { 0 } /\ F = ( z e. CC |-> sum_ k e. ( 0 ... n ) ( ( a ` k ) x. ( z ^ k ) ) ) ) )

  proof
    cF
    cS
    cply
    cfv
    #
    wcel
    #
    va
    cv
    #
    vn
    cv
    #
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    cima
    #
    cc0
    csn
    #
    wceq
    #
    cF
    vz
    cc
    cc0
    @3
    cfz
    co
    #
    vk
    cv
    #
    @2
    cfv
    #
    vz
    cv
    #
    @10
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    #
    wceq
    #
    wa
    #
    vn
    cn0
    wrex
    #
    va
    cc
    cn0
    cmap
    co
    #
    wrex
    #
    @19
    vb
    cv
    #
    vm
    cv
    #
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    cima
    #
    @7
    wceq
    #
    cF
    vz
    cc
    cc0
    @23
    cfz
    co
    #
    @10
    @22
    cfv
    #
    @13
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    #
    wceq
    #
    wa
    #
    vm
    cn0
    wrex
    #
    wa
    #
    @2
    @22
    wceq
    #
    wi
    #
    vb
    @20
    wral
    va
    @20
    wral
    @19
    va
    @20
    wreu
    @1
    @19
    va
    cc
    @7
    cun
    #
    cn0
    cmap
    co
    #
    wrex
    #
    @21
    @1
    cF
    cc
    cply
    cfv
    #
    wcel
    #
    @41
    @0
    @42
    cF
    cS
    plyssc
    sseli
    @43
    @18
    va
    @40
    wrex
    vn
    cn0
    wrex
    #
    @41
    @43
    cc
    cc
    wss
    @44
    vz
    cc
    vk
    vn
    cF
    va
    elply2
    simprbi
    @18
    vn
    va
    cn0
    @40
    rexcom
    sylib
    syl
    @19
    va
    @40
    @20
    @39
    cc
    cn0
    cmap
    @7
    cc
    wss
    #
    @39
    cc
    wceq
    cc0
    cc
    wcel
    @45
    0cn
    cc0
    cc
    snssi
    ax-mp
    @7
    cc
    ssequn2
    mpbi
    oveq1i
    rexeqi
    sylib
    @1
    @38
    va
    vb
    @20
    @20
    @36
    @18
    @34
    wa
    #
    vm
    cn0
    wrex
    vn
    cn0
    wrex
    @1
    @2
    @20
    wcel
    #
    @22
    @20
    wcel
    #
    wa
    #
    wa
    #
    @37
    @18
    @34
    vn
    vm
    cn0
    cn0
    reeanv
    @50
    @46
    @37
    vn
    vm
    cn0
    cn0
    @50
    @3
    cn0
    wcel
    #
    @23
    cn0
    wcel
    #
    wa
    #
    @46
    @37
    @50
    @53
    @46
    w3a
    #
    vw
    @2
    @22
    cS
    vj
    cF
    @3
    @23
    @1
    @49
    @53
    @46
    simp1l
    @47
    @48
    @1
    @53
    @46
    simp1rl
    @47
    @48
    @1
    @53
    @46
    simp1rr
    @50
    @51
    @52
    @46
    simp2l
    @50
    @51
    @52
    @46
    simp2r
    @8
    @17
    @34
    @50
    @53
    simp3ll
    @27
    @33
    @18
    @50
    @53
    simp3rl
    @54
    cF
    @16
    vw
    cc
    @9
    vj
    cv
    #
    @2
    cfv
    #
    vw
    cv
    #
    @55
    cexp
    co
    #
    cmul
    co
    #
    vj
    csu
    #
    cmpt
    @8
    @17
    @34
    @50
    @53
    simp3lr
    vz
    vw
    cc
    @15
    @60
    @12
    @57
    wceq
    #
    @15
    @9
    @11
    @57
    @10
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    @60
    @61
    @9
    @14
    @63
    vk
    @61
    @13
    @62
    @11
    cmul
    @12
    @57
    @10
    cexp
    oveq1
    #
    oveq2d
    sumeq2sdv
    @9
    @63
    @59
    vk
    vj
    @10
    @55
    wceq
    #
    @11
    @56
    @62
    @58
    cmul
    @10
    @55
    @2
    fveq2
    @10
    @55
    @57
    cexp
    oveq2
    #
    oveq12d
    cbvsumv
    syl6eq
    cbvmptv
    syl6eq
    @54
    cF
    @32
    vw
    cc
    @28
    @55
    @22
    cfv
    #
    @58
    cmul
    co
    #
    vj
    csu
    #
    cmpt
    @27
    @33
    @18
    @50
    @53
    simp3rr
    vz
    vw
    cc
    @31
    @69
    @61
    @31
    @28
    @29
    @62
    cmul
    co
    #
    vk
    csu
    @69
    @61
    @28
    @30
    @70
    vk
    @61
    @13
    @62
    @29
    cmul
    @64
    oveq2d
    sumeq2sdv
    @28
    @70
    @68
    vk
    vj
    @65
    @29
    @67
    @62
    @58
    cmul
    @10
    @55
    @22
    fveq2
    @66
    oveq12d
    cbvsumv
    syl6eq
    cbvmptv
    syl6eq
    coeeulem
    3expia
    rexlimdvva
    syl5bir
    ralrimivva
    @19
    @35
    va
    vb
    @20
    @37
    @19
    @22
    @5
    cima
    #
    @7
    wceq
    #
    cF
    vz
    cc
    @9
    @30
    vk
    csu
    #
    cmpt
    #
    wceq
    #
    wa
    #
    vn
    cn0
    wrex
    @35
    @37
    @18
    @76
    vn
    cn0
    @37
    @8
    @72
    @17
    @75
    @37
    @6
    @71
    @7
    @2
    @22
    @5
    imaeq1
    eqeq1d
    @37
    @16
    @74
    cF
    @37
    vz
    cc
    @15
    @73
    @37
    @9
    @14
    @30
    vk
    @37
    @11
    @29
    @13
    cmul
    @10
    @2
    @22
    fveq1
    oveq1d
    sumeq2sdv
    mpteq2dv
    eqeq2d
    anbi12d
    rexbidv
    @76
    @34
    vn
    vm
    cn0
    @3
    @23
    wceq
    #
    @72
    @27
    @75
    @33
    @77
    @71
    @26
    @7
    @77
    @5
    @25
    @22
    @77
    @4
    @24
    cuz
    @3
    @23
    c1
    caddc
    oveq1
    fveq2d
    imaeq2d
    eqeq1d
    @77
    @74
    @32
    cF
    @77
    vz
    cc
    @73
    @31
    @77
    @9
    @28
    @30
    vk
    @3
    @23
    cc0
    cfz
    oveq2
    sumeq1d
    mpteq2dv
    eqeq2d
    anbi12d
    cbvrexv
    syl6bb
    reu4
    sylanbrc
end
