include "cn.mm"
include "c1.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "cesum.mm"
include "cmpt.mm"
include "clm.mm"
include "cfv.mm"
include "wceq.mm"
include "cbvesumv.mm"
include "oveq2.mm"
include "esumeq1.mm"
include "syl.mm"
include "syl5eqr.mm"
include "cbvmptv.mm"
include "esumcvg.mm"
include "syl5eqbrr.mm"

theorem esumcvg2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cJ: class J
  let vl: setvar l
  let vi: setvar i
  assume esumcvg2.j: |- J = ( TopOpen ` ( RR*s |`s ( 0 [,] +oo ) ) )
  assume esumcvg2.a: |- ( ( ph /\ k e. NN ) -> A e. ( 0 [,] +oo ) )
  assume esumcvg2.l: |- ( k = l -> A = B )
  assume esumcvg2.m: |- ( k = m -> A = C )

  disjoint k l
  disjoint k m
  disjoint k n
  disjoint l m
  disjoint l n
  disjoint m n
  disjoint A l
  disjoint A m
  disjoint A n
  disjoint B k
  disjoint B n
  disjoint C k
  disjoint C l
  disjoint C n
  disjoint J k
  disjoint J n
  disjoint k ph
  disjoint l ph
  disjoint n ph
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint i n
  disjoint A i
  assert |- ( ph -> ( n e. NN |-> sum* k e. ( 1 ... n ) A ) ( ~~>t ` J ) sum* k e. NN A )

  proof
    wph
    vn
    cn
    c1
    vn
    cv
    #
    cfz
    co
    #
    cA
    vk
    cesum
    #
    cmpt
    vi
    cn
    c1
    vi
    cv
    #
    cfz
    co
    #
    cC
    vm
    cesum
    #
    cmpt
    #
    cn
    cA
    vk
    cesum
    cJ
    clm
    cfv
    vi
    vn
    cn
    @5
    @2
    @3
    @0
    wceq
    #
    @5
    @4
    cA
    vk
    cesum
    #
    @2
    @4
    cA
    cC
    vk
    vm
    esumcvg2.m
    cbvesumv
    @7
    @4
    @1
    wceq
    @8
    @2
    wceq
    @3
    @0
    c1
    cfz
    oveq2
    @4
    @1
    cA
    vk
    esumeq1
    syl
    syl5eqr
    cbvmptv
    #
    wph
    cA
    cB
    vk
    vl
    vn
    @6
    cJ
    esumcvg2.j
    @9
    esumcvg2.a
    esumcvg2.l
    esumcvg
    syl5eqbrr
end
