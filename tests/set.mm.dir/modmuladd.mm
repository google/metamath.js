include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "cico.mm"
include "co.mm"
include "crp.mm"
include "w3a.mm"
include "cmo.mm"
include "wceq.mm"
include "cv.mm"
include "cmul.mm"
include "caddc.mm"
include "wrex.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "wa.mm"
include "cr.mm"
include "zre.mm"
include "adantr.mm"
include "rpre.mm"
include "adantl.mm"
include "wne.mm"
include "rpne0.mm"
include "redivcld.mm"
include "flcld.mm"
include "3adant2.mm"
include "wb.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "anim1i.mm"
include "flpmodeq.mm"
include "syl.mm"
include "eqcomd.mm"
include "rspcedvd.mm"
include "oveq2.mm"
include "eqcoms.mm"
include "rexbidv.mm"
include "syl5ibrcom.mm"
include "simpr.mm"
include "simpl3.mm"
include "simpl2.mm"
include "muladdmodid.mm"
include "syl3anc.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "rexlimdva.mm"
include "impbid.mm"

theorem modmuladd
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cM: class M

  disjoint A k
  disjoint B k
  disjoint M k
  assert |- ( ( A e. ZZ /\ B e. ( 0 [,) M ) /\ M e. RR+ ) -> ( ( A mod M ) = B <-> E. k e. ZZ A = ( ( k x. M ) + B ) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cc0
    cM
    cico
    co
    wcel
    #
    cM
    crp
    wcel
    #
    w3a
    #
    cA
    cM
    cmo
    co
    #
    cB
    wceq
    #
    cA
    vk
    cv
    #
    cM
    cmul
    co
    #
    cB
    caddc
    co
    #
    wceq
    #
    vk
    cz
    wrex
    #
    @3
    @10
    @5
    cA
    @7
    @4
    caddc
    co
    #
    wceq
    #
    vk
    cz
    wrex
    @3
    @12
    cA
    cA
    cM
    cdiv
    co
    #
    cfl
    cfv
    #
    cM
    cmul
    co
    #
    @4
    caddc
    co
    #
    wceq
    #
    vk
    @14
    cz
    @0
    @2
    @14
    cz
    wcel
    @1
    @0
    @2
    wa
    #
    @13
    @18
    cA
    cM
    @0
    cA
    cr
    wcel
    #
    @2
    cA
    zre
    #
    adantr
    @2
    cM
    cr
    wcel
    @0
    cM
    rpre
    adantl
    @2
    cM
    cc0
    wne
    @0
    cM
    rpne0
    adantl
    redivcld
    flcld
    3adant2
    @6
    @14
    wceq
    #
    @12
    @17
    wb
    @3
    @21
    @11
    @16
    cA
    @21
    @7
    @15
    @4
    caddc
    @6
    @14
    cM
    cmul
    oveq1
    oveq1d
    eqeq2d
    adantl
    @3
    @16
    cA
    @3
    @19
    @2
    wa
    #
    @16
    cA
    wceq
    @0
    @2
    @22
    @1
    @0
    @19
    @2
    @20
    anim1i
    3adant2
    cA
    cM
    flpmodeq
    syl
    eqcomd
    rspcedvd
    @5
    @9
    @12
    vk
    cz
    @9
    @12
    wb
    cB
    @4
    cB
    @4
    wceq
    @8
    @11
    cA
    cB
    @4
    @7
    caddc
    oveq2
    eqeq2d
    eqcoms
    rexbidv
    syl5ibrcom
    @3
    @9
    @5
    vk
    cz
    @3
    @6
    cz
    wcel
    #
    wa
    #
    @9
    @5
    @9
    @24
    @4
    @8
    cM
    cmo
    co
    #
    cB
    cA
    @8
    cM
    cmo
    oveq1
    @24
    @23
    @2
    @1
    @25
    cB
    wceq
    @3
    @23
    simpr
    @0
    @1
    @2
    @23
    simpl3
    @0
    @1
    @2
    @23
    simpl2
    cB
    cM
    @6
    muladdmodid
    syl3anc
    sylan9eqr
    ex
    rexlimdva
    impbid
end
