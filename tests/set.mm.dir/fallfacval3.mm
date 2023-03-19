include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cfallfac.mm"
include "c1.mm"
include "cmin.mm"
include "cv.mm"
include "cprod.mm"
include "cc.mm"
include "cn0.mm"
include "wceq.mm"
include "elfz3nn0.mm"
include "nn0cnd.mm"
include "elfznn0.mm"
include "fallfacval.mm"
include "syl2anc.mm"
include "elfzel2.mm"
include "elfzel1.mm"
include "cz.mm"
include "elfzelz.mm"
include "peano2zm.mm"
include "syl.mm"
include "zcnd.mm"
include "subcl.mm"
include "syl2an.mm"
include "oveq2.mm"
include "fprodrev.mm"
include "subid1d.mm"
include "oveq2d.mm"
include "wa.mm"
include "adantr.mm"
include "adantl.mm"
include "nncand.mm"
include "prodeq12dv.mm"
include "3eqtrd.mm"

theorem fallfacval3
  let cA: class A
  let vk: setvar k
  let cN: class N
  let vj: setvar j

  disjoint A k
  disjoint N k
  disjoint A j
  disjoint j k
  disjoint N j
  assert |- ( N e. ( 0 ... A ) -> ( A FallFac N ) = prod_ k e. ( ( A - ( N - 1 ) ) ... A ) k )

  proof
    cN
    cc0
    cA
    cfz
    co
    wcel
    #
    cA
    cN
    cfallfac
    co
    #
    cc0
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    cA
    vj
    cv
    #
    cmin
    co
    #
    vj
    cprod
    #
    cA
    @2
    cmin
    co
    #
    cA
    cc0
    cmin
    co
    #
    cfz
    co
    #
    cA
    cA
    vk
    cv
    #
    cmin
    co
    #
    cmin
    co
    #
    vk
    cprod
    @7
    cA
    cfz
    co
    #
    @10
    vk
    cprod
    @0
    cA
    cc
    wcel
    #
    cN
    cn0
    wcel
    @1
    @6
    wceq
    @0
    cA
    cN
    cA
    elfz3nn0
    nn0cnd
    #
    cN
    cA
    elfznn0
    cA
    vj
    cN
    fallfacval
    syl2anc
    @0
    @5
    @12
    vj
    vk
    cA
    cc0
    @2
    cN
    cc0
    cA
    elfzel2
    cN
    cc0
    cA
    elfzel1
    @0
    cN
    cz
    wcel
    @2
    cz
    wcel
    cN
    cc0
    cA
    elfzelz
    cN
    peano2zm
    syl
    @0
    @14
    @4
    cc
    wcel
    @5
    cc
    wcel
    @4
    @3
    wcel
    #
    @15
    @16
    @4
    @4
    cc0
    @2
    elfzelz
    zcnd
    cA
    @4
    subcl
    syl2an
    @4
    @11
    cA
    cmin
    oveq2
    fprodrev
    @0
    @9
    @13
    @12
    @10
    vk
    @0
    @8
    cA
    @7
    cfz
    @0
    cA
    @15
    subid1d
    oveq2d
    @0
    @10
    @9
    wcel
    #
    wa
    cA
    @10
    @0
    @14
    @17
    @15
    adantr
    @17
    @10
    cc
    wcel
    @0
    @17
    @10
    @10
    @7
    @8
    elfzelz
    zcnd
    adantl
    nncand
    prodeq12dv
    3eqtrd
end
