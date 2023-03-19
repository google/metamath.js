include "csmu.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "cfv.mm"
include "cn0.mm"
include "crab.mm"
include "smufval.mm"
include "eleq2d.mm"
include "wb.mm"
include "wceq.mm"
include "id.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "eleq12d.mm"
include "elrab3.mm"
include "syl.mm"
include "bitrd.mm"

theorem smuval
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let vm: setvar m
  let vn: setvar n
  let cN: class N
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let cM: class M
  assume smuval.a: |- ( ph -> A C_ NN0 )
  assume smuval.b: |- ( ph -> B C_ NN0 )
  assume smuval.p: |- P = seq 0 ( ( p e. ~P NN0 , m e. NN0 |-> ( p sadd { n e. NN0 | ( m e. A /\ ( n - m ) e. B ) } ) ) , ( n e. NN0 |-> if ( n = 0 , (/) , ( n - 1 ) ) ) )
  assume smuval.n: |- ( ph -> N e. NN0 )

  disjoint m n
  disjoint m p
  disjoint A m
  disjoint n p
  disjoint A n
  disjoint A p
  disjoint N n
  disjoint n ph
  disjoint B m
  disjoint B n
  disjoint B p
  disjoint k m
  disjoint k n
  disjoint k p
  disjoint k x
  disjoint k y
  disjoint A k
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
  disjoint N x
  disjoint N y
  disjoint k ph
  disjoint ph x
  disjoint ph y
  disjoint B k
  disjoint B x
  disjoint B y
  disjoint M k
  disjoint M x
  disjoint P k
  disjoint P x
  disjoint P y
  assert |- ( ph -> ( N e. ( A smul B ) <-> N e. ( P ` ( N + 1 ) ) ) )

  proof
    wph
    cN
    cA
    cB
    csmu
    co
    #
    wcel
    cN
    vk
    cv
    #
    @1
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
    wcel
    #
    cN
    cN
    c1
    caddc
    co
    #
    cP
    cfv
    #
    wcel
    #
    wph
    @0
    @5
    cN
    wph
    cA
    cB
    cP
    vk
    vm
    vn
    vp
    smuval.a
    smuval.b
    smuval.p
    smufval
    eleq2d
    wph
    cN
    cn0
    wcel
    @6
    @9
    wb
    smuval.n
    @4
    @9
    vk
    cN
    cn0
    @1
    cN
    wceq
    #
    @1
    cN
    @3
    @8
    @10
    id
    @10
    @2
    @7
    cP
    @1
    cN
    c1
    caddc
    oveq1
    fveq2d
    eleq12d
    elrab3
    syl
    bitrd
end
