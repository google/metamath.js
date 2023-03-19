include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "cc0.mm"
include "cblen.mm"
include "cfv.mm"
include "cfzo.mm"
include "cv.mm"
include "c2.mm"
include "cdig.mm"
include "cexp.mm"
include "csu.mm"
include "wceq.mm"
include "nn0sumshdig.mm"
include "adantr.mm"
include "oveq1d.mm"
include "cfn.mm"
include "fzofi.mm"
include "a1i.mm"
include "cc.mm"
include "nn0cn.mm"
include "adantl.mm"
include "cn.mm"
include "cz.mm"
include "cpnf.mm"
include "cico.mm"
include "2nn.mm"
include "elfzoelz.mm"
include "nn0rp0.mm"
include "digvalnn0.mm"
include "syl3anc.mm"
include "nn0cnd.mm"
include "2nn0.mm"
include "elfzonn0.mm"
include "nn0expcld.mm"
include "mulcld.mm"
include "fsummulc1.mm"
include "eqtrd.mm"

theorem nn0mullong
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x

  disjoint A k
  disjoint B k
  disjoint k x
  assert |- ( ( A e. NN0 /\ B e. NN0 ) -> ( A x. B ) = sum_ k e. ( 0 ..^ ( #b ` A ) ) ( ( ( k ( digit ` 2 ) A ) x. ( 2 ^ k ) ) x. B ) )

  proof
    cA
    cn0
    wcel
    #
    cB
    cn0
    wcel
    #
    wa
    #
    cA
    cB
    cmul
    co
    cc0
    cA
    cblen
    cfv
    #
    cfzo
    co
    #
    vk
    cv
    #
    cA
    c2
    cdig
    cfv
    co
    #
    c2
    @5
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cB
    cmul
    co
    @4
    @8
    cB
    cmul
    co
    vk
    csu
    @2
    cA
    @9
    cB
    cmul
    @0
    cA
    @9
    wceq
    @1
    cA
    vk
    nn0sumshdig
    adantr
    oveq1d
    @2
    @4
    @8
    cB
    vk
    @4
    cfn
    wcel
    @2
    cc0
    @3
    fzofi
    a1i
    @1
    cB
    cc
    wcel
    @0
    cB
    nn0cn
    adantl
    @2
    @5
    @4
    wcel
    #
    wa
    #
    @6
    @7
    @11
    @6
    @11
    c2
    cn
    wcel
    #
    @5
    cz
    wcel
    #
    cA
    cc0
    cpnf
    cico
    co
    wcel
    #
    @6
    cn0
    wcel
    @12
    @11
    2nn
    a1i
    @10
    @13
    @2
    @5
    cc0
    @3
    elfzoelz
    adantl
    @2
    @14
    @10
    @0
    @14
    @1
    cA
    nn0rp0
    adantr
    adantr
    c2
    cA
    @5
    digvalnn0
    syl3anc
    nn0cnd
    @10
    @7
    cc
    wcel
    @2
    @10
    @7
    @10
    c2
    @5
    c2
    cn0
    wcel
    @10
    2nn0
    a1i
    @5
    @3
    elfzonn0
    nn0expcld
    nn0cnd
    adantl
    mulcld
    fsummulc1
    eqtrd
end
