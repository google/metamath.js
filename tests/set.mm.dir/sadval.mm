include "csad.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "c0.mm"
include "cfv.mm"
include "whad.mm"
include "cn0.mm"
include "crab.mm"
include "sadfval.mm"
include "eleq2d.mm"
include "wb.mm"
include "wceq.mm"
include "eleq1.mm"
include "fveq2.mm"
include "hadbi123d.mm"
include "elrab3.mm"
include "syl.mm"
include "bitrd.mm"

theorem sadval
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vm: setvar m
  let vn: setvar n
  let cN: class N
  let vc: setvar c
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let cK: class K
  assume sadval.a: |- ( ph -> A C_ NN0 )
  assume sadval.b: |- ( ph -> B C_ NN0 )
  assume sadval.c: |- C = seq 0 ( ( c e. 2o , m e. NN0 |-> if ( cadd ( m e. A , m e. B , (/) e. c ) , 1o , (/) ) ) , ( n e. NN0 |-> if ( n = 0 , (/) , ( n - 1 ) ) ) )
  assume sadcp1.n: |- ( ph -> N e. NN0 )

  disjoint c m
  disjoint c n
  disjoint m n
  disjoint A c
  disjoint A m
  disjoint B c
  disjoint B m
  disjoint N n
  disjoint c k
  disjoint c x
  disjoint c y
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint m x
  disjoint m y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint A k
  disjoint A x
  disjoint A y
  disjoint B k
  disjoint B x
  disjoint B y
  disjoint N k
  disjoint N x
  disjoint N y
  disjoint C k
  disjoint C x
  disjoint C y
  disjoint K k
  disjoint K x
  disjoint k ph
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( N e. ( A sadd B ) <-> hadd ( N e. A , N e. B , (/) e. ( C ` N ) ) ) )

  proof
    wph
    cN
    cA
    cB
    csad
    co
    #
    wcel
    cN
    vk
    cv
    #
    cA
    wcel
    #
    @1
    cB
    wcel
    #
    c0
    @1
    cC
    cfv
    #
    wcel
    #
    whad
    #
    vk
    cn0
    crab
    #
    wcel
    #
    cN
    cA
    wcel
    #
    cN
    cB
    wcel
    #
    c0
    cN
    cC
    cfv
    #
    wcel
    #
    whad
    #
    wph
    @0
    @7
    cN
    wph
    cA
    cB
    cC
    vk
    vm
    vn
    vc
    sadval.a
    sadval.b
    sadval.c
    sadfval
    eleq2d
    wph
    cN
    cn0
    wcel
    @8
    @13
    wb
    sadcp1.n
    @6
    @13
    vk
    cN
    cn0
    @1
    cN
    wceq
    #
    @2
    @9
    @3
    @10
    @5
    @12
    @1
    cN
    cA
    eleq1
    @1
    cN
    cB
    eleq1
    @14
    @4
    @11
    c0
    @1
    cN
    cC
    fveq2
    eleq2d
    hadbi123d
    elrab3
    syl
    bitrd
end
