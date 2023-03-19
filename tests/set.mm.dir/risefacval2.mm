include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "crisefac.mm"
include "co.mm"
include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "cv.mm"
include "caddc.mm"
include "cprod.mm"
include "risefacval.mm"
include "1zzd.mm"
include "0zd.mm"
include "cz.mm"
include "nn0z.mm"
include "peano2zm.mm"
include "syl.mm"
include "adantl.mm"
include "simpl.mm"
include "elfznn0.mm"
include "nn0cnd.mm"
include "addcl.mm"
include "syl2an.mm"
include "oveq2.mm"
include "fprodshft.mm"
include "wceq.mm"
include "0p1e1.mm"
include "a1i.mm"
include "nn0cn.mm"
include "1cnd.mm"
include "npcand.mm"
include "oveq12d.mm"
include "prodeq1d.mm"
include "3eqtrd.mm"

theorem risefacval2
  let cA: class A
  let vk: setvar k
  let cN: class N
  let vn: setvar n

  disjoint A k
  disjoint N k
  disjoint A n
  disjoint k n
  disjoint N n
  assert |- ( ( A e. CC /\ N e. NN0 ) -> ( A RiseFac N ) = prod_ k e. ( 1 ... N ) ( A + ( k - 1 ) ) )

  proof
    cA
    cc
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cA
    cN
    crisefac
    co
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
    vn
    cv
    #
    caddc
    co
    #
    vn
    cprod
    cc0
    c1
    caddc
    co
    #
    @3
    c1
    caddc
    co
    #
    cfz
    co
    #
    cA
    vk
    cv
    c1
    cmin
    co
    #
    caddc
    co
    #
    vk
    cprod
    c1
    cN
    cfz
    co
    #
    @11
    vk
    cprod
    cA
    vn
    cN
    risefacval
    @2
    @6
    @11
    vn
    vk
    c1
    cc0
    @3
    @2
    1zzd
    @2
    0zd
    @1
    @3
    cz
    wcel
    #
    @0
    @1
    cN
    cz
    wcel
    @13
    cN
    nn0z
    cN
    peano2zm
    syl
    adantl
    @2
    @0
    @5
    cc
    wcel
    @6
    cc
    wcel
    @5
    @4
    wcel
    #
    @0
    @1
    simpl
    @14
    @5
    @5
    @3
    elfznn0
    nn0cnd
    cA
    @5
    addcl
    syl2an
    @5
    @10
    cA
    caddc
    oveq2
    fprodshft
    @2
    @9
    @12
    @11
    vk
    @2
    @7
    c1
    @8
    cN
    cfz
    @7
    c1
    wceq
    @2
    0p1e1
    a1i
    @1
    @8
    cN
    wceq
    @0
    @1
    cN
    c1
    cN
    nn0cn
    @1
    1cnd
    npcand
    adantl
    oveq12d
    prodeq1d
    3eqtrd
end
