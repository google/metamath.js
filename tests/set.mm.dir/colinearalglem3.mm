include "cee.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "c1.mm"
include "cfz.mm"
include "wral.mm"
include "colinearalglem2.mm"
include "wb.mm"
include "3comr.mm"
include "bitrd.mm"

theorem colinearalglem3
  let cA: class A
  let cB: class B
  let cC: class C
  let vi: setvar i
  let vj: setvar j
  let cN: class N

  disjoint A i
  disjoint A j
  disjoint i j
  disjoint B i
  disjoint B j
  disjoint C i
  disjoint C j
  disjoint N i
  disjoint N j
  assert |- ( ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) -> ( A. i e. ( 1 ... N ) A. j e. ( 1 ... N ) ( ( ( B ` i ) - ( A ` i ) ) x. ( ( C ` j ) - ( A ` j ) ) ) = ( ( ( B ` j ) - ( A ` j ) ) x. ( ( C ` i ) - ( A ` i ) ) ) <-> A. i e. ( 1 ... N ) A. j e. ( 1 ... N ) ( ( ( A ` i ) - ( C ` i ) ) x. ( ( B ` j ) - ( C ` j ) ) ) = ( ( ( A ` j ) - ( C ` j ) ) x. ( ( B ` i ) - ( C ` i ) ) ) ) )

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
    cC
    @0
    wcel
    #
    w3a
    vi
    cv
    #
    cB
    cfv
    #
    @4
    cA
    cfv
    #
    cmin
    co
    vj
    cv
    #
    cC
    cfv
    #
    @7
    cA
    cfv
    #
    cmin
    co
    cmul
    co
    @7
    cB
    cfv
    #
    @9
    cmin
    co
    @4
    cC
    cfv
    #
    @6
    cmin
    co
    cmul
    co
    wceq
    vj
    c1
    cN
    cfz
    co
    #
    wral
    vi
    @12
    wral
    @11
    @5
    cmin
    co
    @9
    @10
    cmin
    co
    cmul
    co
    @8
    @10
    cmin
    co
    @6
    @5
    cmin
    co
    cmul
    co
    wceq
    vj
    @12
    wral
    vi
    @12
    wral
    #
    @6
    @11
    cmin
    co
    @10
    @8
    cmin
    co
    cmul
    co
    @9
    @8
    cmin
    co
    @5
    @11
    cmin
    co
    cmul
    co
    wceq
    vj
    @12
    wral
    vi
    @12
    wral
    #
    cA
    cB
    cC
    vi
    vj
    cN
    colinearalglem2
    @2
    @3
    @1
    @13
    @14
    wb
    cB
    cC
    cA
    vi
    vj
    cN
    colinearalglem2
    3comr
    bitrd
end
