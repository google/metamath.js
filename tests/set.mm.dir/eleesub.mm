include "cee.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cmin.mm"
include "cmpt.mm"
include "cr.mm"
include "wral.mm"
include "fveere.mm"
include "resubcl.mm"
include "syl2an.mm"
include "anandirs.mm"
include "ralrimiva.mm"
include "wb.mm"
include "cn.mm"
include "eleenn.mm"
include "mptelee.mm"
include "syl.mm"
include "adantr.mm"
include "mpbird.mm"
include "syl5eqel.mm"

theorem eleesub
  let cA: class A
  let cB: class B
  let cC: class C
  let vi: setvar i
  let cN: class N
  assume eleesub.1: |- C = ( i e. ( 1 ... N ) |-> ( ( A ` i ) - ( B ` i ) ) )

  disjoint N i
  disjoint A i
  disjoint B i
  assert |- ( ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) -> C e. ( EE ` N ) )

  proof
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    cC
    vi
    c1
    cN
    cfz
    co
    #
    vi
    cv
    #
    cA
    cfv
    #
    @5
    cB
    cfv
    #
    cmin
    co
    #
    cmpt
    #
    @0
    eleesub.1
    @3
    @9
    @0
    wcel
    #
    @8
    cr
    wcel
    #
    vi
    @4
    wral
    #
    @3
    @11
    vi
    @4
    @1
    @2
    @5
    @4
    wcel
    #
    @11
    @1
    @13
    wa
    @6
    cr
    wcel
    @7
    cr
    wcel
    @11
    @2
    @13
    wa
    cA
    @5
    cN
    fveere
    cB
    @5
    cN
    fveere
    @6
    @7
    resubcl
    syl2an
    anandirs
    ralrimiva
    @1
    @10
    @12
    wb
    #
    @2
    @1
    cN
    cn
    wcel
    @14
    cA
    cN
    eleenn
    @6
    @7
    vi
    cmin
    cN
    mptelee
    syl
    adantr
    mpbird
    syl5eqel
end
