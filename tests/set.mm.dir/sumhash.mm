include "cfn.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "c1.mm"
include "csu.mm"
include "chash.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cv.mm"
include "cc0.mm"
include "cif.mm"
include "cc.mm"
include "wceq.mm"
include "ssfi.mm"
include "ax-1cn.mm"
include "fsumconst.mm"
include "sylancl.mm"
include "wral.mm"
include "cuz.mm"
include "wo.mm"
include "simpr.mm"
include "rgenw.mm"
include "a1i.mm"
include "simpl.mm"
include "olcd.mm"
include "sumss2.mm"
include "syl21anc.mm"
include "cn0.mm"
include "hashcl.mm"
include "syl.mm"
include "nn0cnd.mm"
include "mulid1d.mm"
include "3eqtr3d.mm"

theorem sumhash
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cC: class C

  disjoint A k
  disjoint B k
  assert |- ( ( B e. Fin /\ A C_ B ) -> sum_ k e. B if ( k e. A , 1 , 0 ) = ( # ` A ) )

  proof
    cB
    cfn
    wcel
    #
    cA
    cB
    wss
    #
    wa
    #
    cA
    c1
    vk
    csu
    #
    cA
    chash
    cfv
    #
    c1
    cmul
    co
    #
    cB
    vk
    cv
    cA
    wcel
    c1
    cc0
    cif
    vk
    csu
    #
    @4
    @2
    cA
    cfn
    wcel
    #
    c1
    cc
    wcel
    #
    @3
    @5
    wceq
    cB
    cA
    ssfi
    #
    ax-1cn
    cA
    c1
    vk
    fsumconst
    sylancl
    @2
    @1
    @8
    vk
    cA
    wral
    #
    cB
    cC
    cuz
    cfv
    wss
    #
    @0
    wo
    @3
    @6
    wceq
    @0
    @1
    simpr
    @10
    @2
    @8
    vk
    cA
    ax-1cn
    rgenw
    a1i
    @2
    @0
    @11
    @0
    @1
    simpl
    olcd
    cA
    cB
    c1
    vk
    cC
    sumss2
    syl21anc
    @2
    @4
    @2
    @4
    @2
    @7
    @4
    cn0
    wcel
    @9
    cA
    hashcl
    syl
    nn0cnd
    mulid1d
    3eqtr3d
end
