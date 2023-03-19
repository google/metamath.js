include "cmd.mm"
include "wbr.mm"
include "cin.mm"
include "cv.mm"
include "wss.mm"
include "wa.mm"
include "chj.mm"
include "co.mm"
include "wi.mm"
include "cch.mm"
include "wral.mm"
include "wceq.mm"
include "mdsl2i.mm"
include "wcel.mm"
include "wb.mm"
include "chincli.mm"
include "w3a.mm"
include "inss1.mm"
include "chlej2.mm"
include "mpan2.mm"
include "mp3an12.mm"
include "adantr.mm"
include "simpr.mm"
include "inss2.mm"
include "jctir.mm"
include "chlub.mm"
include "mp3an23.mm"
include "mpbid.mm"
include "ssind.mm"
include "biantrud.mm"
include "eqss.mm"
include "syl6bbr.mm"
include "ex.mm"
include "adantld.mm"
include "pm5.74d.mm"
include "ralbiia.mm"
include "bitri.mm"

theorem mdsl2bi
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume mdsl.1: |- A e. CH
  assume mdsl.2: |- B e. CH

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( A MH B <-> A. x e. CH ( ( ( A i^i B ) C_ x /\ x C_ B ) -> ( ( x vH A ) i^i B ) = ( x vH ( A i^i B ) ) ) )

  proof
    cA
    cB
    cmd
    wbr
    cA
    cB
    cin
    #
    vx
    cv
    #
    wss
    #
    @1
    cB
    wss
    #
    wa
    #
    @1
    cA
    chj
    co
    #
    cB
    cin
    #
    @1
    @0
    chj
    co
    #
    wss
    #
    wi
    #
    vx
    cch
    wral
    @4
    @6
    @7
    wceq
    #
    wi
    #
    vx
    cch
    wral
    vx
    cA
    cB
    mdsl.1
    mdsl.2
    mdsl2i
    @9
    @11
    vx
    cch
    @1
    cch
    wcel
    #
    @4
    @8
    @10
    @12
    @3
    @8
    @10
    wb
    #
    @2
    @12
    @3
    @13
    @12
    @3
    wa
    #
    @8
    @8
    @7
    @6
    wss
    #
    wa
    @10
    @14
    @15
    @8
    @14
    @7
    @5
    cB
    @12
    @7
    @5
    wss
    #
    @3
    @0
    cch
    wcel
    #
    cA
    cch
    wcel
    #
    @12
    @16
    cA
    cB
    mdsl.1
    mdsl.2
    chincli
    #
    mdsl.1
    @17
    @18
    @12
    w3a
    @0
    cA
    wss
    @16
    cA
    cB
    inss1
    @0
    cA
    @1
    chlej2
    mpan2
    mp3an12
    adantr
    @14
    @3
    @0
    cB
    wss
    #
    wa
    #
    @7
    cB
    wss
    #
    @14
    @3
    @20
    @12
    @3
    simpr
    cA
    cB
    inss2
    jctir
    @12
    @21
    @22
    wb
    #
    @3
    @12
    @17
    cB
    cch
    wcel
    @23
    @19
    mdsl.2
    @1
    @0
    cB
    chlub
    mp3an23
    adantr
    mpbid
    ssind
    biantrud
    @6
    @7
    eqss
    syl6bbr
    ex
    adantld
    pm5.74d
    ralbiia
    bitri
end
