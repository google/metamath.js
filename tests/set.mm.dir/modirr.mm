include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "cdiv.mm"
include "co.mm"
include "cq.mm"
include "cdif.mm"
include "cmo.mm"
include "cc0.mm"
include "wne.mm"
include "wn.mm"
include "wa.mm"
include "eldif.mm"
include "wceq.mm"
include "cfl.mm"
include "cfv.mm"
include "cmul.mm"
include "cmin.mm"
include "modval.mm"
include "eqeq1d.mm"
include "cc.mm"
include "recn.mm"
include "adantr.mm"
include "rpre.mm"
include "adantl.mm"
include "refldivcl.mm"
include "remulcld.mm"
include "recnd.mm"
include "subeq0ad.mm"
include "eqcom.mm"
include "wb.mm"
include "rerpdivcl.mm"
include "reflcl.mm"
include "syl.mm"
include "rpcnne0.mm"
include "divmul2.mm"
include "syl3anc.mm"
include "syl5rbbr.mm"
include "3bitrd.mm"
include "wi.mm"
include "cz.mm"
include "flidz.mm"
include "zq.mm"
include "syl6bi.mm"
include "sylbid.mm"
include "necon3bd.mm"
include "adantld.mm"
include "syl5bi.mm"
include "3impia.mm"

theorem modirr
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR+ /\ ( A / B ) e. ( RR \ QQ ) ) -> ( A mod B ) =/= 0 )

  proof
    cA
    cr
    wcel
    #
    cB
    crp
    wcel
    #
    cA
    cB
    cdiv
    co
    #
    cr
    cq
    cdif
    wcel
    #
    cA
    cB
    cmo
    co
    #
    cc0
    wne
    #
    @3
    @2
    cr
    wcel
    #
    @2
    cq
    wcel
    #
    wn
    #
    wa
    @0
    @1
    wa
    #
    @5
    @2
    cr
    cq
    eldif
    @9
    @8
    @5
    @6
    @9
    @7
    @4
    cc0
    @9
    @4
    cc0
    wceq
    #
    @2
    cfl
    cfv
    #
    @2
    wceq
    #
    @7
    @9
    @10
    cA
    cB
    @11
    cmul
    co
    #
    cmin
    co
    #
    cc0
    wceq
    cA
    @13
    wceq
    #
    @12
    @9
    @4
    @14
    cc0
    cA
    cB
    modval
    eqeq1d
    @9
    cA
    @13
    @0
    cA
    cc
    wcel
    #
    @1
    cA
    recn
    adantr
    #
    @9
    @13
    @9
    cB
    @11
    @1
    cB
    cr
    wcel
    @0
    cB
    rpre
    adantl
    cA
    cB
    refldivcl
    remulcld
    recnd
    subeq0ad
    @12
    @2
    @11
    wceq
    #
    @9
    @15
    @2
    @11
    eqcom
    @9
    @16
    @11
    cc
    wcel
    #
    cB
    cc
    wcel
    cB
    cc0
    wne
    wa
    #
    @18
    @15
    wb
    @17
    @9
    @6
    @19
    cA
    cB
    rerpdivcl
    #
    @6
    @11
    @2
    reflcl
    recnd
    syl
    @1
    @20
    @0
    cB
    rpcnne0
    adantl
    cA
    @11
    cB
    divmul2
    syl3anc
    syl5rbbr
    3bitrd
    @9
    @6
    @12
    @7
    wi
    @21
    @6
    @12
    @2
    cz
    wcel
    @7
    @2
    flidz
    @2
    zq
    syl6bi
    syl
    sylbid
    necon3bd
    adantld
    syl5bi
    3impia
end
