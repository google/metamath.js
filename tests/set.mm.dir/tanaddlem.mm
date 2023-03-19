include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "ccos.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "caddc.mm"
include "co.mm"
include "ctan.mm"
include "cmul.mm"
include "c1.mm"
include "csin.mm"
include "cmin.mm"
include "wceq.mm"
include "coscl.mm"
include "ad2antrr.mm"
include "ad2antlr.mm"
include "mulcld.mm"
include "sincl.mm"
include "subeq0ad.mm"
include "cosadd.mm"
include "adantr.mm"
include "eqeq1d.mm"
include "cdiv.mm"
include "tanval.mm"
include "ad2ant2r.mm"
include "ad2ant2l.mm"
include "oveq12d.mm"
include "simprl.mm"
include "simprr.mm"
include "divmuldivd.mm"
include "eqtrd.mm"
include "1cnd.mm"
include "mulne0d.mm"
include "divmuld.mm"
include "mulid1d.mm"
include "3bitrd.mm"
include "3bitr4d.mm"
include "necon3bid.mm"

theorem tanaddlem
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. CC /\ B e. CC ) /\ ( ( cos ` A ) =/= 0 /\ ( cos ` B ) =/= 0 ) ) -> ( ( cos ` ( A + B ) ) =/= 0 <-> ( ( tan ` A ) x. ( tan ` B ) ) =/= 1 ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    ccos
    cfv
    #
    cc0
    wne
    #
    cB
    ccos
    cfv
    #
    cc0
    wne
    #
    wa
    #
    wa
    #
    cA
    cB
    caddc
    co
    ccos
    cfv
    #
    cc0
    cA
    ctan
    cfv
    #
    cB
    ctan
    cfv
    #
    cmul
    co
    #
    c1
    @8
    @3
    @5
    cmul
    co
    #
    cA
    csin
    cfv
    #
    cB
    csin
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    cc0
    wceq
    @13
    @16
    wceq
    #
    @9
    cc0
    wceq
    @12
    c1
    wceq
    #
    @8
    @13
    @16
    @8
    @3
    @5
    @0
    @3
    cc
    wcel
    @1
    @7
    cA
    coscl
    ad2antrr
    #
    @1
    @5
    cc
    wcel
    @0
    @7
    cB
    coscl
    ad2antlr
    #
    mulcld
    #
    @8
    @14
    @15
    @0
    @14
    cc
    wcel
    @1
    @7
    cA
    sincl
    ad2antrr
    #
    @1
    @15
    cc
    wcel
    @0
    @7
    cB
    sincl
    ad2antlr
    #
    mulcld
    #
    subeq0ad
    @8
    @9
    @17
    cc0
    @2
    @9
    @17
    wceq
    @7
    cA
    cB
    cosadd
    adantr
    eqeq1d
    @8
    @19
    @16
    @13
    cdiv
    co
    #
    c1
    wceq
    @13
    c1
    cmul
    co
    #
    @16
    wceq
    @18
    @8
    @12
    @26
    c1
    @8
    @12
    @14
    @3
    cdiv
    co
    #
    @15
    @5
    cdiv
    co
    #
    cmul
    co
    @26
    @8
    @10
    @28
    @11
    @29
    cmul
    @0
    @4
    @10
    @28
    wceq
    @1
    @6
    cA
    tanval
    ad2ant2r
    @1
    @6
    @11
    @29
    wceq
    @0
    @4
    cB
    tanval
    ad2ant2l
    oveq12d
    @8
    @14
    @3
    @15
    @5
    @23
    @20
    @24
    @21
    @2
    @4
    @6
    simprl
    #
    @2
    @4
    @6
    simprr
    #
    divmuldivd
    eqtrd
    eqeq1d
    @8
    @16
    @13
    c1
    @25
    @22
    @8
    1cnd
    @8
    @3
    @5
    @20
    @21
    @30
    @31
    mulne0d
    divmuld
    @8
    @27
    @13
    @16
    @8
    @13
    @22
    mulid1d
    eqeq1d
    3bitrd
    3bitr4d
    necon3bid
end
