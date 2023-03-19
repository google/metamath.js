include "cn0.mm"
include "wcel.mm"
include "cr.mm"
include "wa.mm"
include "cdp2.mm"
include "c10.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cdp.mm"
include "cdc.mm"
include "dfdp2OLD.mm"
include "dpval.mm"
include "cc.mm"
include "wceq.mm"
include "nn0cn.mm"
include "recn.mm"
include "cmul.mm"
include "dfdecOLD.mm"
include "oveq1i.mm"
include "10reOLD.mm"
include "recni.mm"
include "mulcl.mm"
include "mpan.mm"
include "cc0.mm"
include "wne.mm"
include "10posOLD.mm"
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

theorem dpfrac1OLD
  let cA: class A
  let cB: class B


  assert |- ( ( A e. NN0 /\ B e. RR ) -> ( A . B ) = ( ; A B / 10 ) )

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
    c10
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
    c10
    cdiv
    co
    #
    cA
    cB
    dfdp2OLD
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
    @5
    @3
    wceq
    @1
    cA
    nn0cn
    cB
    recn
    @6
    @7
    wa
    #
    @5
    c10
    cA
    cmul
    co
    #
    cB
    caddc
    co
    #
    c10
    cdiv
    co
    #
    @3
    @4
    @10
    c10
    cdiv
    cA
    cB
    dfdecOLD
    oveq1i
    @8
    @11
    @9
    c10
    cdiv
    co
    #
    @2
    caddc
    co
    #
    @3
    @6
    @9
    cc
    wcel
    #
    @7
    @11
    @13
    wceq
    #
    c10
    cc
    wcel
    #
    @6
    @14
    c10
    10reOLD
    recni
    #
    c10
    cA
    mulcl
    mpan
    @14
    @7
    @16
    c10
    cc0
    wne
    #
    wa
    @15
    @16
    @18
    @17
    c10
    10reOLD
    10posOLD
    gt0ne0ii
    #
    pm3.2i
    @9
    cB
    c10
    divdir
    mp3an3
    sylan
    @6
    @13
    @3
    wceq
    @7
    @6
    @12
    cA
    @2
    caddc
    @6
    @16
    @18
    @12
    cA
    wceq
    @17
    @19
    cA
    c10
    divcan3
    mp3an23
    oveq1d
    adantr
    eqtrd
    syl5eq
    syl2an
    3eqtr4a
end
