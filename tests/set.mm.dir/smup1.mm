include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cn0.mm"
include "cpw.mm"
include "cv.mm"
include "wcel.mm"
include "cmin.mm"
include "wa.mm"
include "crab.mm"
include "csad.mm"
include "cmpt2.mm"
include "cc0.mm"
include "wceq.mm"
include "c0.mm"
include "cif.mm"
include "cmpt.mm"
include "cseq.mm"
include "cfv.mm"
include "cfzo.mm"
include "cin.mm"
include "csmu.mm"
include "eqid.mm"
include "smupp1.mm"
include "peano2nn0.mm"
include "syl.mm"
include "smupval.mm"
include "oveq1d.mm"
include "3eqtr3d.mm"

theorem smup1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vn: setvar n
  let cN: class N
  let vm: setvar m
  let vp: setvar p
  assume smup1.a: |- ( ph -> A C_ NN0 )
  assume smup1.b: |- ( ph -> B C_ NN0 )
  assume smup1.n: |- ( ph -> N e. NN0 )

  disjoint A n
  disjoint B n
  disjoint N n
  disjoint n ph
  disjoint m n
  disjoint m p
  disjoint A m
  disjoint n p
  disjoint A p
  disjoint B m
  disjoint B p
  disjoint N m
  disjoint N p
  assert |- ( ph -> ( ( A i^i ( 0 ..^ ( N + 1 ) ) ) smul B ) = ( ( ( A i^i ( 0 ..^ N ) ) smul B ) sadd { n e. NN0 | ( N e. A /\ ( n - N ) e. B ) } ) )

  proof
    wph
    cN
    c1
    caddc
    co
    #
    vp
    vm
    cn0
    cpw
    cn0
    vp
    cv
    vm
    cv
    #
    cA
    wcel
    vn
    cv
    #
    @1
    cmin
    co
    cB
    wcel
    wa
    vn
    cn0
    crab
    csad
    co
    cmpt2
    vn
    cn0
    @2
    cc0
    wceq
    c0
    @2
    c1
    cmin
    co
    cif
    cmpt
    cc0
    cseq
    #
    cfv
    cN
    @3
    cfv
    #
    cN
    cA
    wcel
    @2
    cN
    cmin
    co
    cB
    wcel
    wa
    vn
    cn0
    crab
    #
    csad
    co
    cA
    cc0
    @0
    cfzo
    co
    cin
    cB
    csmu
    co
    cA
    cc0
    cN
    cfzo
    co
    cin
    cB
    csmu
    co
    #
    @5
    csad
    co
    wph
    cA
    cB
    @3
    vm
    vn
    cN
    vp
    smup1.a
    smup1.b
    @3
    eqid
    #
    smup1.n
    smupp1
    wph
    cA
    cB
    @3
    vm
    vn
    @0
    vp
    smup1.a
    smup1.b
    @7
    wph
    cN
    cn0
    wcel
    @0
    cn0
    wcel
    smup1.n
    cN
    peano2nn0
    syl
    smupval
    wph
    @4
    @6
    @5
    csad
    wph
    cA
    cB
    @3
    vm
    vn
    cN
    vp
    smup1.a
    smup1.b
    @7
    smup1.n
    smupval
    oveq1d
    3eqtr3d
end
