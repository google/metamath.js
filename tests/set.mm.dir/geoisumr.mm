include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "cv.mm"
include "cexp.mm"
include "cmin.mm"
include "cn0.mm"
include "cmpt.mm"
include "cc0.mm"
include "nn0uz.mm"
include "0zd.mm"
include "wceq.mm"
include "oveq2.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "wne.mm"
include "cle.mm"
include "wn.mm"
include "0le1.mm"
include "0re.mm"
include "1re.mm"
include "lenlti.mm"
include "mpbi.mm"
include "fveq2.mm"
include "abs0.mm"
include "syl6eq.mm"
include "breq2d.mm"
include "mtbiri.mm"
include "necon2ai.mm"
include "reccl.mm"
include "sylan2.mm"
include "expcl.mm"
include "sylan.mm"
include "simpl.mm"
include "simpr.mm"
include "georeclim.mm"
include "isumclim.mm"

theorem geoisumr
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let cR: class R

  disjoint A k
  disjoint k n
  disjoint A n
  disjoint R k
  disjoint R n
  assert |- ( ( A e. CC /\ 1 < ( abs ` A ) ) -> sum_ k e. NN0 ( ( 1 / A ) ^ k ) = ( A / ( A - 1 ) ) )

  proof
    cA
    cc
    wcel
    #
    c1
    cA
    cabs
    cfv
    #
    clt
    wbr
    #
    wa
    #
    c1
    cA
    cdiv
    co
    #
    vk
    cv
    #
    cexp
    co
    #
    cA
    cA
    c1
    cmin
    co
    cdiv
    co
    vk
    vn
    cn0
    @4
    vn
    cv
    #
    cexp
    co
    #
    cmpt
    #
    cc0
    cn0
    nn0uz
    @3
    0zd
    @5
    cn0
    wcel
    #
    @5
    @9
    cfv
    @6
    wceq
    @3
    vn
    @5
    @8
    @6
    cn0
    @9
    @7
    @5
    @4
    cexp
    oveq2
    @9
    eqid
    @4
    @5
    cexp
    ovex
    fvmpt
    adantl
    #
    @3
    @4
    cc
    wcel
    #
    @10
    @6
    cc
    wcel
    @2
    @0
    cA
    cc0
    wne
    @12
    @2
    cA
    cc0
    cA
    cc0
    wceq
    #
    @2
    c1
    cc0
    clt
    wbr
    #
    cc0
    c1
    cle
    wbr
    @14
    wn
    0le1
    cc0
    c1
    0re
    1re
    lenlti
    mpbi
    @13
    @1
    cc0
    c1
    clt
    @13
    @1
    cc0
    cabs
    cfv
    cc0
    cA
    cc0
    cabs
    fveq2
    abs0
    syl6eq
    breq2d
    mtbiri
    necon2ai
    cA
    reccl
    sylan2
    @4
    @5
    expcl
    sylan
    @3
    cA
    vk
    @9
    @0
    @2
    simpl
    @0
    @2
    simpr
    @11
    georeclim
    isumclim
end
