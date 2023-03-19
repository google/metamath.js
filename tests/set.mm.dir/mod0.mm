include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cmo.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cz.mm"
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
include "bitrd.mm"
include "eqcom.mm"
include "wne.mm"
include "wb.mm"
include "rpcnne0.mm"
include "divmul2.mm"
include "syl3anc.mm"
include "syl5rbbr.mm"
include "rerpdivcl.mm"
include "flidz.mm"
include "syl.mm"

theorem mod0
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR+ ) -> ( ( A mod B ) = 0 <-> ( A / B ) e. ZZ ) )

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
    cc0
    wceq
    #
    cA
    cB
    cdiv
    co
    #
    cfl
    cfv
    #
    @5
    wceq
    #
    @5
    cz
    wcel
    #
    @2
    @4
    cA
    cB
    @6
    cmul
    co
    #
    wceq
    #
    @7
    @2
    @4
    cA
    @9
    cmin
    co
    #
    cc0
    wceq
    @10
    @2
    @3
    @11
    cc0
    cA
    cB
    modval
    eqeq1d
    @2
    cA
    @9
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
    @2
    @9
    @2
    cB
    @6
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
    #
    remulcld
    recnd
    subeq0ad
    bitrd
    @7
    @5
    @6
    wceq
    #
    @2
    @10
    @5
    @6
    eqcom
    @2
    @12
    @6
    cc
    wcel
    cB
    cc
    wcel
    cB
    cc0
    wne
    wa
    #
    @15
    @10
    wb
    @13
    @2
    @6
    @14
    recnd
    @1
    @16
    @0
    cB
    rpcnne0
    adantl
    cA
    @6
    cB
    divmul2
    syl3anc
    syl5rbbr
    bitrd
    @2
    @5
    cr
    wcel
    @7
    @8
    wb
    cA
    cB
    rerpdivcl
    @5
    flidz
    syl
    bitrd
end
