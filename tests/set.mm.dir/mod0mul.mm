include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cmo.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "cdiv.mm"
include "cv.mm"
include "cmul.mm"
include "wrex.mm"
include "cr.mm"
include "crp.mm"
include "wb.mm"
include "zre.mm"
include "nnrp.mm"
include "mod0.mm"
include "syl2an.mm"
include "simpr.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "adantl.mm"
include "cc.mm"
include "zcn.mm"
include "adantr.mm"
include "nncn.mm"
include "wne.mm"
include "nnne0.mm"
include "divcan1d.mm"
include "eqcomd.mm"
include "rspcedvd.mm"
include "ex.mm"
include "sylbid.mm"

theorem mod0mul
  let vx: setvar x
  let cA: class A
  let cN: class N
  let vk: setvar k

  disjoint A x
  disjoint N x
  disjoint k x
  assert |- ( ( A e. ZZ /\ N e. NN ) -> ( ( A mod N ) = 0 -> E. x e. ZZ A = ( x x. N ) ) )

  proof
    cA
    cz
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    cA
    cN
    cmo
    co
    cc0
    wceq
    #
    cA
    cN
    cdiv
    co
    #
    cz
    wcel
    #
    cA
    vx
    cv
    #
    cN
    cmul
    co
    #
    wceq
    #
    vx
    cz
    wrex
    #
    @0
    cA
    cr
    wcel
    cN
    crp
    wcel
    @3
    @5
    wb
    @1
    cA
    zre
    cN
    nnrp
    cA
    cN
    mod0
    syl2an
    @2
    @5
    @9
    @2
    @5
    wa
    #
    @8
    cA
    @4
    cN
    cmul
    co
    #
    wceq
    #
    vx
    @4
    cz
    @2
    @5
    simpr
    @6
    @4
    wceq
    #
    @8
    @12
    wb
    @10
    @13
    @7
    @11
    cA
    @6
    @4
    cN
    cmul
    oveq1
    eqeq2d
    adantl
    @10
    @11
    cA
    @2
    @11
    cA
    wceq
    @5
    @2
    cA
    cN
    @0
    cA
    cc
    wcel
    @1
    cA
    zcn
    adantr
    @1
    cN
    cc
    wcel
    @0
    cN
    nncn
    adantl
    @1
    cN
    cc0
    wne
    @0
    cN
    nnne0
    adantl
    divcan1d
    adantr
    eqcomd
    rspcedvd
    ex
    sylbid
end
