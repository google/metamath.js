include "ccoe.mm"
include "cfv.mm"
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
include "crio.mm"
include "cply.mm"
include "wcel.mm"
include "coeval.mm"
include "syl.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "imaeq2d.mm"
include "eqeq1d.mm"
include "oveq2.mm"
include "sumeq1d.mm"
include "mpteq2dv.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "wreu.mm"
include "wb.mm"
include "wf.mm"
include "cnex.mm"
include "nn0ex.mm"
include "elmap.mm"
include "sylibr.mm"
include "coeeu.mm"
include "imaeq1.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "sumeq2sdv.mm"
include "rexbidv.mm"
include "riota2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "eqtrd.mm"

theorem coeeq
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cN: class N
  let va: setvar a
  let vn: setvar n
  assume coeeq.1: |- ( ph -> F e. ( Poly ` S ) )
  assume coeeq.2: |- ( ph -> N e. NN0 )
  assume coeeq.3: |- ( ph -> A : NN0 --> CC )
  assume coeeq.4: |- ( ph -> ( A " ( ZZ>= ` ( N + 1 ) ) ) = { 0 } )
  assume coeeq.5: |- ( ph -> F = ( z e. CC |-> sum_ k e. ( 0 ... N ) ( ( A ` k ) x. ( z ^ k ) ) ) )

  disjoint k z
  disjoint A k
  disjoint A z
  disjoint N k
  disjoint N z
  disjoint a k
  disjoint a n
  disjoint a z
  disjoint A a
  disjoint k n
  disjoint n z
  disjoint A n
  disjoint F a
  disjoint F n
  disjoint N n
  disjoint S a
  disjoint S n
  assert |- ( ph -> ( coeff ` F ) = A )

  proof
    wph
    cF
    ccoe
    cfv
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
    @2
    cfz
    co
    #
    vk
    cv
    #
    @1
    cfv
    #
    vz
    cv
    @9
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
    crio
    #
    cA
    wph
    cF
    cS
    cply
    cfv
    wcel
    #
    @0
    @19
    wceq
    coeeq.1
    vz
    cS
    vk
    vn
    cF
    va
    coeval
    syl
    wph
    cA
    @4
    cima
    #
    @6
    wceq
    #
    cF
    vz
    cc
    @8
    @9
    cA
    cfv
    #
    @11
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
    @19
    cA
    wceq
    #
    wph
    cN
    cn0
    wcel
    cA
    cN
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    cima
    #
    @6
    wceq
    #
    cF
    vz
    cc
    cc0
    cN
    cfz
    co
    #
    @24
    vk
    csu
    #
    cmpt
    #
    wceq
    #
    @29
    coeeq.2
    coeeq.4
    coeeq.5
    @28
    @34
    @38
    wa
    vn
    cN
    cn0
    @2
    cN
    wceq
    #
    @22
    @34
    @27
    @38
    @39
    @21
    @33
    @6
    @39
    @4
    @32
    cA
    @39
    @3
    @31
    cuz
    @2
    cN
    c1
    caddc
    oveq1
    fveq2d
    imaeq2d
    eqeq1d
    @39
    @26
    @37
    cF
    @39
    vz
    cc
    @25
    @36
    @39
    @8
    @35
    @24
    vk
    @2
    cN
    cc0
    cfz
    oveq2
    sumeq1d
    mpteq2dv
    eqeq2d
    anbi12d
    rspcev
    syl12anc
    wph
    cA
    @18
    wcel
    #
    @17
    va
    @18
    wreu
    #
    @29
    @30
    wb
    wph
    cn0
    cc
    cA
    wf
    @40
    coeeq.3
    cc
    cn0
    cA
    cnex
    nn0ex
    elmap
    sylibr
    wph
    @20
    @41
    coeeq.1
    vz
    cS
    vk
    vn
    cF
    va
    coeeu
    syl
    @17
    @29
    va
    @18
    cA
    @1
    cA
    wceq
    #
    @16
    @28
    vn
    cn0
    @42
    @7
    @22
    @15
    @27
    @42
    @5
    @21
    @6
    @1
    cA
    @4
    imaeq1
    eqeq1d
    @42
    @14
    @26
    cF
    @42
    vz
    cc
    @13
    @25
    @42
    @8
    @12
    @24
    vk
    @42
    @10
    @23
    @11
    cmul
    @9
    @1
    cA
    fveq1
    oveq1d
    sumeq2sdv
    mpteq2dv
    eqeq2d
    anbi12d
    rexbidv
    riota2
    syl2anc
    mpbid
    eqtrd
end
