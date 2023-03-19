include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cn.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "csu.mm"
include "cmin.mm"
include "cdiv.mm"
include "cmpt.mm"
include "nnuz.mm"
include "1zzd.mm"
include "wceq.mm"
include "oveq2.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "cn0.mm"
include "simpl.mm"
include "nnnn0.mm"
include "expcl.mm"
include "syl2an.mm"
include "simpr.mm"
include "1nn0.mm"
include "a1i.mm"
include "cuz.mm"
include "elnnuz.mm"
include "sylan2br.mm"
include "geolim2.mm"
include "isumclim.mm"
include "exp1.mm"
include "adantr.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem geoisum1
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let cR: class R

  disjoint A k
  disjoint k n
  disjoint A n
  disjoint R k
  disjoint R n
  assert |- ( ( A e. CC /\ ( abs ` A ) < 1 ) -> sum_ k e. NN ( A ^ k ) = ( A / ( 1 - A ) ) )

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
    cn
    cA
    vk
    cv
    #
    cexp
    co
    #
    vk
    csu
    cA
    c1
    cexp
    co
    #
    c1
    cA
    cmin
    co
    #
    cdiv
    co
    #
    cA
    @6
    cdiv
    co
    @2
    @4
    @7
    vk
    vn
    cn
    cA
    vn
    cv
    #
    cexp
    co
    #
    cmpt
    #
    c1
    cn
    nnuz
    @2
    1zzd
    @3
    cn
    wcel
    #
    @3
    @10
    cfv
    @4
    wceq
    #
    @2
    vn
    @3
    @9
    @4
    cn
    @10
    @8
    @3
    cA
    cexp
    oveq2
    @10
    eqid
    cA
    @3
    cexp
    ovex
    fvmpt
    adantl
    #
    @2
    @0
    @3
    cn0
    wcel
    @4
    cc
    wcel
    @11
    @0
    @1
    simpl
    #
    @3
    nnnn0
    cA
    @3
    expcl
    syl2an
    @2
    cA
    vk
    @10
    c1
    @14
    @0
    @1
    simpr
    c1
    cn0
    wcel
    @2
    1nn0
    a1i
    @3
    c1
    cuz
    cfv
    wcel
    @2
    @11
    @12
    @3
    elnnuz
    @13
    sylan2br
    geolim2
    isumclim
    @2
    @5
    cA
    @6
    cdiv
    @0
    @5
    cA
    wceq
    @1
    cA
    exp1
    adantr
    oveq1d
    eqtrd
end
