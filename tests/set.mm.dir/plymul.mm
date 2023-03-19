include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cuz.mm"
include "cfv.mm"
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
include "cun.mm"
include "cn0.mm"
include "cmap.mm"
include "wrex.mm"
include "cof.mm"
include "cply.mm"
include "wcel.mm"
include "wss.mm"
include "elply2.mm"
include "simprbi.mm"
include "syl.mm"
include "reeanv.mm"
include "w3a.mm"
include "simp1l.mm"
include "sylan.mm"
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
include "plymullem.mm"
include "3expia.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "mp2and.mm"

theorem plymul
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cF: class F
  let cG: class G
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vz: setvar z
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vj: setvar j
  let vw: setvar w
  let cA: class A
  let cM: class M
  let cN: class N
  assume plyadd.1: |- ( ph -> F e. ( Poly ` S ) )
  assume plyadd.2: |- ( ph -> G e. ( Poly ` S ) )
  assume plyadd.3: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x + y ) e. S )
  assume plymul.4: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x x. y ) e. S )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint S x
  disjoint S y
  disjoint G x
  disjoint G y
  disjoint ph x
  disjoint ph y
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint B k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint B m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint B n
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint a b
  disjoint a j
  disjoint a m
  disjoint a n
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint F a
  disjoint b j
  disjoint b m
  disjoint b n
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint F b
  disjoint j m
  disjoint j n
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint F j
  disjoint m w
  disjoint F m
  disjoint n w
  disjoint F n
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint F z
  disjoint a k
  disjoint S a
  disjoint b k
  disjoint S b
  disjoint j k
  disjoint S j
  disjoint k w
  disjoint S k
  disjoint S m
  disjoint S n
  disjoint S w
  disjoint S z
  disjoint A m
  disjoint A n
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint G a
  disjoint G b
  disjoint G j
  disjoint G m
  disjoint G n
  disjoint G w
  disjoint G z
  disjoint a ph
  disjoint b ph
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph w
  disjoint ph z
  disjoint M k
  disjoint M m
  disjoint M n
  disjoint M z
  disjoint N k
  disjoint N m
  disjoint N n
  disjoint N z
  assert |- ( ph -> ( F oF x. G ) e. ( Poly ` S ) )

  proof
    wph
    va
    cv
    #
    vm
    cv
    #
    c1
    caddc
    co
    cuz
    cfv
    cima
    cc0
    csn
    #
    wceq
    #
    cF
    vz
    cc
    cc0
    @1
    cfz
    co
    #
    vk
    cv
    #
    @0
    cfv
    #
    vz
    cv
    #
    @5
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
    va
    cS
    @2
    cun
    cn0
    cmap
    co
    #
    wrex
    #
    vm
    cn0
    wrex
    #
    vb
    cv
    #
    vn
    cv
    #
    c1
    caddc
    co
    cuz
    cfv
    cima
    @2
    wceq
    #
    cG
    vz
    cc
    cc0
    @18
    cfz
    co
    #
    @5
    @17
    cfv
    #
    @8
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
    vb
    @14
    wrex
    #
    vn
    cn0
    wrex
    #
    cF
    cG
    cmul
    cof
    co
    cS
    cply
    cfv
    #
    wcel
    #
    wph
    cF
    @29
    wcel
    #
    @16
    plyadd.1
    @31
    cS
    cc
    wss
    #
    @16
    vz
    cS
    vk
    vm
    cF
    va
    elply2
    simprbi
    syl
    wph
    cG
    @29
    wcel
    #
    @28
    plyadd.2
    @33
    @32
    @28
    vz
    cS
    vk
    vn
    cG
    vb
    elply2
    simprbi
    syl
    @16
    @28
    wa
    @15
    @27
    wa
    #
    vn
    cn0
    wrex
    vm
    cn0
    wrex
    wph
    @30
    @15
    @27
    vm
    vn
    cn0
    cn0
    reeanv
    wph
    @34
    @30
    vm
    vn
    cn0
    cn0
    @34
    @13
    @26
    wa
    #
    vb
    @14
    wrex
    va
    @14
    wrex
    wph
    @1
    cn0
    wcel
    #
    @18
    cn0
    wcel
    #
    wa
    #
    wa
    #
    @30
    @13
    @26
    va
    vb
    @14
    @14
    reeanv
    @39
    @35
    @30
    va
    vb
    @14
    @14
    @39
    @0
    @14
    wcel
    #
    @17
    @14
    wcel
    #
    wa
    #
    @35
    @30
    @39
    @42
    @35
    w3a
    #
    vx
    vy
    vw
    @0
    @17
    cS
    vj
    cF
    cG
    @1
    @18
    @43
    wph
    @31
    wph
    @38
    @42
    @35
    simp1l
    #
    plyadd.1
    syl
    @43
    wph
    @33
    @44
    plyadd.2
    syl
    @43
    wph
    vx
    cv
    #
    cS
    wcel
    vy
    cv
    #
    cS
    wcel
    wa
    #
    @45
    @46
    caddc
    co
    cS
    wcel
    @44
    plyadd.3
    sylan
    @36
    @37
    wph
    @42
    @35
    simp1rl
    @36
    @37
    wph
    @42
    @35
    simp1rr
    @39
    @40
    @41
    @35
    simp2l
    @39
    @40
    @41
    @35
    simp2r
    @3
    @12
    @26
    @39
    @42
    simp3ll
    @19
    @25
    @13
    @39
    @42
    simp3rl
    @43
    cF
    @11
    vw
    cc
    @4
    vj
    cv
    #
    @0
    cfv
    #
    vw
    cv
    #
    @48
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
    @3
    @12
    @26
    @39
    @42
    simp3lr
    vz
    vw
    cc
    @10
    @53
    @7
    @50
    wceq
    #
    @10
    @4
    @6
    @50
    @5
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    @53
    @54
    @4
    @9
    @56
    vk
    @54
    @8
    @55
    @6
    cmul
    @7
    @50
    @5
    cexp
    oveq1
    #
    oveq2d
    sumeq2sdv
    @4
    @56
    @52
    vk
    vj
    @5
    @48
    wceq
    #
    @6
    @49
    @55
    @51
    cmul
    @5
    @48
    @0
    fveq2
    @5
    @48
    @50
    cexp
    oveq2
    #
    oveq12d
    cbvsumv
    syl6eq
    cbvmptv
    syl6eq
    @43
    cG
    @24
    vw
    cc
    @20
    @48
    @17
    cfv
    #
    @51
    cmul
    co
    #
    vj
    csu
    #
    cmpt
    @19
    @25
    @13
    @39
    @42
    simp3rr
    vz
    vw
    cc
    @23
    @62
    @54
    @23
    @20
    @21
    @55
    cmul
    co
    #
    vk
    csu
    @62
    @54
    @20
    @22
    @63
    vk
    @54
    @8
    @55
    @21
    cmul
    @57
    oveq2d
    sumeq2sdv
    @20
    @63
    @61
    vk
    vj
    @58
    @21
    @60
    @55
    @51
    cmul
    @5
    @48
    @17
    fveq2
    @59
    oveq12d
    cbvsumv
    syl6eq
    cbvmptv
    syl6eq
    @43
    wph
    @47
    @45
    @46
    cmul
    co
    cS
    wcel
    @44
    plymul.4
    sylan
    plymullem
    3expia
    rexlimdvva
    syl5bir
    rexlimdvva
    syl5bir
    mp2and
end
