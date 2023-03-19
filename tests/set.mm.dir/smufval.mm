include "cn0.mm"
include "cpw.mm"
include "wcel.mm"
include "csmu.mm"
include "co.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "cfv.mm"
include "crab.mm"
include "wceq.mm"
include "wss.mm"
include "nn0ex.mm"
include "elpw2.mm"
include "sylibr.mm"
include "cmin.mm"
include "wa.mm"
include "csad.mm"
include "cmpt2.mm"
include "cc0.mm"
include "c0.mm"
include "cif.mm"
include "cmpt.mm"
include "cseq.mm"
include "w3a.mm"
include "simp1l.mm"
include "eleq2d.mm"
include "simp1r.mm"
include "anbi12d.mm"
include "rabbidv.mm"
include "oveq2d.mm"
include "mpt2eq3dva.mm"
include "seqeq2d.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "df-smu.mm"
include "rabex.mm"
include "ovmpt2a.mm"
include "syl2anc.mm"

theorem smufval
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let vx: setvar x
  let vy: setvar y
  let cN: class N
  let cM: class M
  assume smuval.a: |- ( ph -> A C_ NN0 )
  assume smuval.b: |- ( ph -> B C_ NN0 )
  assume smuval.p: |- P = seq 0 ( ( p e. ~P NN0 , m e. NN0 |-> ( p sadd { n e. NN0 | ( m e. A /\ ( n - m ) e. B ) } ) ) , ( n e. NN0 |-> if ( n = 0 , (/) , ( n - 1 ) ) ) )

  disjoint k m
  disjoint k n
  disjoint k p
  disjoint A k
  disjoint m n
  disjoint m p
  disjoint A m
  disjoint n p
  disjoint A n
  disjoint A p
  disjoint k ph
  disjoint n ph
  disjoint B k
  disjoint B m
  disjoint B n
  disjoint B p
  disjoint P k
  disjoint k x
  disjoint k y
  disjoint m x
  disjoint m y
  disjoint n x
  disjoint n y
  disjoint p x
  disjoint p y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint N k
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint ph x
  disjoint ph y
  disjoint B x
  disjoint B y
  disjoint M k
  disjoint M x
  disjoint P x
  disjoint P y
  assert |- ( ph -> ( A smul B ) = { k e. NN0 | k e. ( P ` ( k + 1 ) ) } )

  proof
    wph
    cA
    cn0
    cpw
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cA
    cB
    csmu
    co
    vk
    cv
    #
    @3
    c1
    caddc
    co
    #
    cP
    cfv
    #
    wcel
    #
    vk
    cn0
    crab
    #
    wceq
    wph
    cA
    cn0
    wss
    @1
    smuval.a
    cA
    cn0
    nn0ex
    elpw2
    sylibr
    wph
    cB
    cn0
    wss
    @2
    smuval.b
    cB
    cn0
    nn0ex
    elpw2
    sylibr
    vx
    vy
    cA
    cB
    @0
    @0
    @3
    @4
    vp
    vm
    @0
    cn0
    vp
    cv
    #
    vm
    cv
    #
    vx
    cv
    #
    wcel
    #
    vn
    cv
    #
    @9
    cmin
    co
    #
    vy
    cv
    #
    wcel
    #
    wa
    #
    vn
    cn0
    crab
    #
    csad
    co
    #
    cmpt2
    #
    vn
    cn0
    @12
    cc0
    wceq
    c0
    @12
    c1
    cmin
    co
    cif
    cmpt
    #
    cc0
    cseq
    #
    cfv
    #
    wcel
    #
    vk
    cn0
    crab
    @7
    csmu
    @10
    cA
    wceq
    #
    @14
    cB
    wceq
    #
    wa
    #
    @23
    @6
    vk
    cn0
    @26
    @22
    @5
    @3
    @26
    @4
    @21
    cP
    @26
    @21
    vp
    vm
    @0
    cn0
    @8
    @9
    cA
    wcel
    #
    @13
    cB
    wcel
    #
    wa
    #
    vn
    cn0
    crab
    #
    csad
    co
    #
    cmpt2
    #
    @20
    cc0
    cseq
    cP
    @26
    @19
    @32
    @20
    cc0
    @26
    vp
    vm
    @0
    cn0
    @18
    @31
    @26
    @8
    @0
    wcel
    #
    @9
    cn0
    wcel
    #
    w3a
    #
    @17
    @30
    @8
    csad
    @35
    @16
    @29
    vn
    cn0
    @35
    @11
    @27
    @15
    @28
    @35
    @10
    cA
    @9
    @24
    @25
    @33
    @34
    simp1l
    eleq2d
    @35
    @14
    cB
    @13
    @24
    @25
    @33
    @34
    simp1r
    eleq2d
    anbi12d
    rabbidv
    oveq2d
    mpt2eq3dva
    seqeq2d
    smuval.p
    syl6eqr
    fveq1d
    eleq2d
    rabbidv
    vx
    vy
    vk
    vm
    vn
    vp
    df-smu
    @6
    vk
    cn0
    nn0ex
    rabex
    ovmpt2a
    syl2anc
end
