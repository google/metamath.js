include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cmo.mm"
include "co.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cmin.mm"
include "cmul.mm"
include "clt.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "recn.mm"
include "rpcnne0.mm"
include "divcan2.mm"
include "3expb.mm"
include "syl2an.mm"
include "oveq1d.mm"
include "rpcn.mm"
include "adantl.mm"
include "rerpdivcl.mm"
include "recnd.mm"
include "refldivcl.mm"
include "subdid.mm"
include "modval.mm"
include "3eqtr4rd.mm"
include "wbr.mm"
include "c1.mm"
include "fraclt1.mm"
include "syl.mm"
include "divid.mm"
include "breqtrrd.mm"
include "wb.mm"
include "resubcld.mm"
include "rpre.mm"
include "rpregt0.mm"
include "ltmuldiv2.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "eqbrtrd.mm"

theorem modlt
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR+ ) -> ( A mod B ) < B )

  proof
    cA
    cr
    wcel
    #
    cB
    crp
    wcel
    #
    wa
    #
    cA
    cB
    cmo
    co
    #
    cB
    cA
    cB
    cdiv
    co
    #
    @4
    cfl
    cfv
    #
    cmin
    co
    #
    cmul
    co
    #
    cB
    clt
    @2
    cB
    @4
    cmul
    co
    #
    cB
    @5
    cmul
    co
    #
    cmin
    co
    cA
    @9
    cmin
    co
    @7
    @3
    @2
    @8
    cA
    @9
    cmin
    @0
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    wa
    #
    @8
    cA
    wceq
    #
    @1
    cA
    recn
    cB
    rpcnne0
    #
    @10
    @11
    @12
    @14
    cA
    cB
    divcan2
    3expb
    syl2an
    oveq1d
    @2
    cB
    @4
    @5
    @1
    @11
    @0
    cB
    rpcn
    adantl
    @2
    @4
    cA
    cB
    rerpdivcl
    #
    recnd
    @2
    @5
    cA
    cB
    refldivcl
    #
    recnd
    subdid
    cA
    cB
    modval
    3eqtr4rd
    @2
    @7
    cB
    clt
    wbr
    #
    @6
    cB
    cB
    cdiv
    co
    #
    clt
    wbr
    #
    @2
    @6
    c1
    @19
    clt
    @2
    @4
    cr
    wcel
    @6
    c1
    clt
    wbr
    @16
    @4
    fraclt1
    syl
    @1
    @19
    c1
    wceq
    #
    @0
    @1
    @13
    @21
    @15
    cB
    divid
    syl
    adantl
    breqtrrd
    @2
    @6
    cr
    wcel
    cB
    cr
    wcel
    #
    @22
    cc0
    cB
    clt
    wbr
    wa
    #
    @18
    @20
    wb
    @2
    @4
    @5
    @16
    @17
    resubcld
    @1
    @22
    @0
    cB
    rpre
    adantl
    @1
    @23
    @0
    cB
    rpregt0
    adantl
    @6
    cB
    cB
    ltmuldiv2
    syl3anc
    mpbird
    eqbrtrd
end
