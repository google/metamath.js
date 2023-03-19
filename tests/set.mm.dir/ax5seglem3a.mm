include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "cv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cmin.mm"
include "cr.mm"
include "simpl21.mm"
include "fveere.mm"
include "sylancom.mm"
include "simpl23.mm"
include "resubcld.mm"
include "simpl31.mm"
include "simpl33.mm"
include "jca.mm"

theorem ax5seglem3a
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vj: setvar j
  let cE: class E
  let cF: class F
  let cN: class N


  assert |- ( ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\ ( D e. ( EE ` N ) /\ E e. ( EE ` N ) /\ F e. ( EE ` N ) ) ) /\ j e. ( 1 ... N ) ) -> ( ( ( A ` j ) - ( C ` j ) ) e. RR /\ ( ( D ` j ) - ( F ` j ) ) e. RR ) )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    cC
    @1
    wcel
    #
    w3a
    #
    cD
    @1
    wcel
    #
    cE
    @1
    wcel
    #
    cF
    @1
    wcel
    #
    w3a
    #
    w3a
    #
    vj
    cv
    #
    c1
    cN
    cfz
    co
    wcel
    #
    wa
    #
    @11
    cA
    cfv
    #
    @11
    cC
    cfv
    #
    cmin
    co
    cr
    wcel
    @11
    cD
    cfv
    #
    @11
    cF
    cfv
    #
    cmin
    co
    cr
    wcel
    @13
    @14
    @15
    @10
    @12
    @2
    @14
    cr
    wcel
    @2
    @3
    @4
    @0
    @9
    @12
    simpl21
    cA
    @11
    cN
    fveere
    sylancom
    @10
    @12
    @4
    @15
    cr
    wcel
    @2
    @3
    @4
    @0
    @9
    @12
    simpl23
    cC
    @11
    cN
    fveere
    sylancom
    resubcld
    @13
    @16
    @17
    @10
    @12
    @6
    @16
    cr
    wcel
    @6
    @7
    @8
    @0
    @5
    @12
    simpl31
    cD
    @11
    cN
    fveere
    sylancom
    @10
    @12
    @8
    @17
    cr
    wcel
    @6
    @7
    @8
    @0
    @5
    @12
    simpl33
    cF
    @11
    cN
    fveere
    sylancom
    resubcld
    jca
end
