include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn.mm"
include "crab.mm"
include "cmu.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "csu.mm"
include "c1.mm"
include "csn.mm"
include "wcel.mm"
include "cc0.mm"
include "cif.mm"
include "wa.mm"
include "wceq.mm"
include "sselda.mm"
include "musum.mm"
include "syl.mm"
include "oveq1d.mm"
include "cfz.mm"
include "cfn.mm"
include "wss.mm"
include "fzfid.mm"
include "dvdsssfz1.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "cc.mm"
include "cz.mm"
include "elrabi.mm"
include "mucl.mm"
include "zcnd.mm"
include "adantl.mm"
include "fsummulc1.mm"
include "ovif.mm"
include "wb.mm"
include "velsn.mm"
include "bicomi.mm"
include "a1i.mm"
include "mulid2.mm"
include "mul02.mm"
include "ifbieq12d.mm"
include "syl5eq.mm"
include "3eqtr3d.mm"
include "sumeq2dv.mm"
include "wral.mm"
include "cuz.mm"
include "wo.mm"
include "snssd.mm"
include "syldan.mm"
include "ralrimiva.mm"
include "olcd.mm"
include "sumss2.mm"
include "syl21anc.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "sumsn.mm"
include "3eqtr2d.mm"

theorem musumsum
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vj: setvar j
  let cF: class F
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vz: setvar z
  let cN: class N
  assume musumsum.1: |- ( m = 1 -> B = C )
  assume musumsum.2: |- ( ph -> A e. Fin )
  assume musumsum.3: |- ( ph -> A C_ NN )
  assume musumsum.4: |- ( ph -> 1 e. A )
  assume musumsum.5: |- ( ( ph /\ m e. A ) -> B e. CC )

  disjoint k m
  disjoint A k
  disjoint A m
  disjoint k n
  disjoint m n
  disjoint k ph
  disjoint m ph
  disjoint B k
  disjoint C m
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint F j
  disjoint F k
  disjoint F m
  disjoint F n
  disjoint j p
  disjoint j q
  disjoint j s
  disjoint j x
  disjoint j z
  disjoint N j
  disjoint k p
  disjoint k q
  disjoint k s
  disjoint k x
  disjoint k z
  disjoint N k
  disjoint m p
  disjoint m q
  disjoint m s
  disjoint m x
  disjoint m z
  disjoint N m
  disjoint n p
  disjoint n q
  disjoint n s
  disjoint n x
  disjoint n z
  disjoint N n
  disjoint p q
  disjoint p s
  disjoint p x
  disjoint p z
  disjoint N p
  disjoint q s
  disjoint q x
  disjoint q z
  disjoint N q
  disjoint s x
  disjoint s z
  disjoint N s
  disjoint x z
  disjoint N x
  disjoint N z
  disjoint j ph
  assert |- ( ph -> sum_ m e. A sum_ k e. { n e. NN | n || m } ( ( mmu ` k ) x. B ) = C )

  proof
    wph
    cA
    vn
    cv
    vm
    cv
    #
    cdvds
    wbr
    #
    vn
    cn
    crab
    #
    vk
    cv
    #
    cmu
    cfv
    #
    cB
    cmul
    co
    vk
    csu
    #
    vm
    csu
    cA
    @0
    c1
    csn
    #
    wcel
    #
    cB
    cc0
    cif
    #
    vm
    csu
    #
    @6
    cB
    vm
    csu
    #
    cC
    wph
    cA
    @5
    @8
    vm
    wph
    @0
    cA
    wcel
    #
    wa
    #
    @2
    @4
    vk
    csu
    #
    cB
    cmul
    co
    @0
    c1
    wceq
    #
    c1
    cc0
    cif
    #
    cB
    cmul
    co
    #
    @5
    @8
    @12
    @13
    @15
    cB
    cmul
    @12
    @0
    cn
    wcel
    #
    @13
    @15
    wceq
    wph
    cA
    cn
    @0
    musumsum.3
    sselda
    #
    vk
    vn
    @0
    musum
    syl
    oveq1d
    @12
    @2
    @4
    cB
    vk
    @12
    c1
    @0
    cfz
    co
    #
    cfn
    wcel
    @2
    @19
    wss
    #
    @2
    cfn
    wcel
    @12
    c1
    @0
    fzfid
    @12
    @17
    @20
    @18
    @0
    vn
    dvdsssfz1
    syl
    @19
    @2
    ssfi
    syl2anc
    musumsum.5
    @3
    @2
    wcel
    #
    @4
    cc
    wcel
    @12
    @21
    @4
    @21
    @3
    cn
    wcel
    @4
    cz
    wcel
    @1
    vn
    @3
    cn
    elrabi
    @3
    mucl
    syl
    zcnd
    adantl
    fsummulc1
    @12
    @16
    @14
    c1
    cB
    cmul
    co
    #
    cc0
    cB
    cmul
    co
    #
    cif
    #
    @8
    @14
    c1
    cc0
    cB
    cmul
    ovif
    @12
    cB
    cc
    wcel
    #
    @24
    @8
    wceq
    musumsum.5
    @25
    @14
    @7
    @22
    @23
    cB
    cc0
    @14
    @7
    wb
    @25
    @7
    @14
    vm
    c1
    velsn
    bicomi
    a1i
    cB
    mulid2
    cB
    mul02
    ifbieq12d
    syl
    syl5eq
    3eqtr3d
    sumeq2dv
    wph
    @6
    cA
    wss
    @25
    vm
    @6
    wral
    cA
    c1
    cuz
    cfv
    wss
    #
    cA
    cfn
    wcel
    #
    wo
    @10
    @9
    wceq
    wph
    c1
    cA
    musumsum.4
    snssd
    #
    wph
    @25
    vm
    @6
    wph
    @7
    @11
    @25
    wph
    @6
    cA
    @0
    @28
    sselda
    musumsum.5
    syldan
    ralrimiva
    wph
    @27
    @26
    musumsum.2
    olcd
    @6
    cA
    cB
    vm
    c1
    sumss2
    syl21anc
    wph
    c1
    cA
    wcel
    #
    cC
    cc
    wcel
    #
    @10
    cC
    wceq
    musumsum.4
    wph
    @29
    @25
    vm
    cA
    wral
    @30
    musumsum.4
    wph
    @25
    vm
    cA
    musumsum.5
    ralrimiva
    @25
    @30
    vm
    c1
    cA
    @14
    cB
    cC
    cc
    musumsum.1
    eleq1d
    rspcv
    sylc
    cB
    cC
    vm
    c1
    cA
    musumsum.1
    sumsn
    syl2anc
    3eqtr2d
end
