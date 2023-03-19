include "cn0.mm"
include "wcel.mm"
include "cr.mm"
include "wa.mm"
include "cdp2.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cdp.mm"
include "df-dp2.mm"
include "dpval.mm"
include "cc.mm"
include "wceq.mm"
include "nn0cn.mm"
include "recn.mm"
include "cmul.mm"
include "dfdec10.mm"
include "oveq1i.mm"
include "10re.mm"
include "recni.mm"
include "a1i.mm"
include "id.mm"
include "mulcld.mm"
include "wne.mm"
include "10pos.mm"
include "gt0ne0ii.mm"
include "pm3.2i.mm"
include "divdir.mm"
include "mp3an3.mm"
include "sylan.mm"
include "divcan3.mm"
include "mp3an23.mm"
include "oveq1d.mm"
include "adantr.mm"
include "eqtrd.mm"
include "syl5eq.mm"
include "syl2an.mm"
include "3eqtr4a.mm"

theorem dpfrac1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. NN0 /\ B e. RR ) -> ( A . B ) = ( ; A B / ; 1 0 ) )

  proof
    cA
    cn0
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    cA
    cB
    cdp2
    cA
    cB
    c1
    cc0
    cdc
    #
    cdiv
    co
    #
    caddc
    co
    #
    cA
    cB
    cdp
    co
    cA
    cB
    cdc
    #
    @2
    cdiv
    co
    #
    cA
    cB
    df-dp2
    cA
    cB
    dpval
    @0
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    @6
    @4
    wceq
    @1
    cA
    nn0cn
    cB
    recn
    @7
    @8
    wa
    #
    @6
    @2
    cA
    cmul
    co
    #
    cB
    caddc
    co
    #
    @2
    cdiv
    co
    #
    @4
    @5
    @11
    @2
    cdiv
    cA
    cB
    dfdec10
    oveq1i
    @9
    @12
    @10
    @2
    cdiv
    co
    #
    @3
    caddc
    co
    #
    @4
    @7
    @10
    cc
    wcel
    #
    @8
    @12
    @14
    wceq
    #
    @7
    @2
    cA
    @2
    cc
    wcel
    #
    @7
    @2
    10re
    recni
    #
    a1i
    @7
    id
    mulcld
    @15
    @8
    @17
    @2
    cc0
    wne
    #
    wa
    @16
    @17
    @19
    @18
    @2
    10re
    10pos
    gt0ne0ii
    #
    pm3.2i
    @10
    cB
    @2
    divdir
    mp3an3
    sylan
    @7
    @14
    @4
    wceq
    @8
    @7
    @13
    cA
    @3
    caddc
    @7
    @17
    @19
    @13
    cA
    wceq
    @18
    @20
    cA
    @2
    divcan3
    mp3an23
    oveq1d
    adantr
    eqtrd
    syl5eq
    syl2an
    3eqtr4a
end
