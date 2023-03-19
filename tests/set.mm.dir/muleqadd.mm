include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "caddc.mm"
include "cc0.mm"
include "ax-1cn.mm"
include "mulsub.mm"
include "mpanr2.mm"
include "mpanl2.mm"
include "mulid1i.mm"
include "oveq2i.mm"
include "a1i.mm"
include "mulid1.mm"
include "oveqan12d.mm"
include "oveq12d.mm"
include "mulcl.mm"
include "addcl.mm"
include "addsub.mm"
include "mp3an2.mm"
include "syl2anc.mm"
include "3eqtrd.mm"
include "eqeq1d.mm"
include "addid2i.mm"
include "eqeq2i.mm"
include "wb.mm"
include "subcld.mm"
include "0cn.mm"
include "addcan2.mm"
include "mp3an23.mm"
include "syl.mm"
include "syl5rbbr.mm"
include "subeq0ad.mm"
include "3bitr2rd.mm"

theorem muleqadd
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( A x. B ) = ( A + B ) <-> ( ( A - 1 ) x. ( B - 1 ) ) = 1 ) )

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
    c1
    cmin
    co
    cB
    c1
    cmin
    co
    cmul
    co
    #
    c1
    wceq
    cA
    cB
    cmul
    co
    #
    cA
    cB
    caddc
    co
    #
    cmin
    co
    #
    c1
    caddc
    co
    #
    c1
    wceq
    #
    @6
    cc0
    wceq
    #
    @4
    @5
    wceq
    @2
    @3
    @7
    c1
    @2
    @3
    @4
    c1
    c1
    cmul
    co
    #
    caddc
    co
    #
    cA
    c1
    cmul
    co
    #
    cB
    c1
    cmul
    co
    #
    caddc
    co
    #
    cmin
    co
    #
    @4
    c1
    caddc
    co
    #
    @5
    cmin
    co
    #
    @7
    @0
    c1
    cc
    wcel
    #
    @1
    @3
    @15
    wceq
    #
    ax-1cn
    @0
    @18
    wa
    @1
    @18
    @19
    ax-1cn
    cA
    c1
    cB
    c1
    mulsub
    mpanr2
    mpanl2
    @2
    @11
    @16
    @14
    @5
    cmin
    @11
    @16
    wceq
    @2
    @10
    c1
    @4
    caddc
    c1
    ax-1cn
    mulid1i
    oveq2i
    a1i
    @0
    @1
    @12
    cA
    @13
    cB
    caddc
    cA
    mulid1
    cB
    mulid1
    oveqan12d
    oveq12d
    @2
    @4
    cc
    wcel
    #
    @5
    cc
    wcel
    #
    @17
    @7
    wceq
    #
    cA
    cB
    mulcl
    #
    cA
    cB
    addcl
    #
    @20
    @18
    @21
    @22
    ax-1cn
    @4
    c1
    @5
    addsub
    mp3an2
    syl2anc
    3eqtrd
    eqeq1d
    @8
    @7
    cc0
    c1
    caddc
    co
    #
    wceq
    #
    @2
    @9
    @25
    c1
    @7
    c1
    ax-1cn
    addid2i
    eqeq2i
    @2
    @6
    cc
    wcel
    #
    @26
    @9
    wb
    #
    @2
    @4
    @5
    @23
    @24
    subcld
    @27
    cc0
    cc
    wcel
    @18
    @28
    0cn
    ax-1cn
    @6
    cc0
    c1
    addcan2
    mp3an23
    syl
    syl5rbbr
    @2
    @4
    @5
    @23
    @24
    subeq0ad
    3bitr2rd
end
