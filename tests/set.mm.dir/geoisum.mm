include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cmin.mm"
include "cdiv.mm"
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
include "expcl.mm"
include "adantlr.mm"
include "simpl.mm"
include "simpr.mm"
include "geolim.mm"
include "isumclim.mm"

theorem geoisum
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let cR: class R

  disjoint A k
  disjoint k n
  disjoint A n
  disjoint R k
  disjoint R n
  assert |- ( ( A e. CC /\ ( abs ` A ) < 1 ) -> sum_ k e. NN0 ( A ^ k ) = ( 1 / ( 1 - A ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cabs
    cfv
    c1
    clt
    wbr
    #
    wa
    #
    cA
    vk
    cv
    #
    cexp
    co
    #
    c1
    c1
    cA
    cmin
    co
    cdiv
    co
    vk
    vn
    cn0
    cA
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
    @2
    0zd
    @3
    cn0
    wcel
    #
    @3
    @7
    cfv
    @4
    wceq
    @2
    vn
    @3
    @6
    @4
    cn0
    @7
    @5
    @3
    cA
    cexp
    oveq2
    @7
    eqid
    cA
    @3
    cexp
    ovex
    fvmpt
    adantl
    #
    @0
    @8
    @4
    cc
    wcel
    @1
    cA
    @3
    expcl
    adantlr
    @2
    cA
    vk
    @7
    @0
    @1
    simpl
    @0
    @1
    simpr
    @9
    geolim
    isumclim
end
