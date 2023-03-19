include "cr.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cneg.mm"
include "caddc.mm"
include "cc.mm"
include "wa.mm"
include "wceq.mm"
include "recn.mm"
include "nn0cn.mm"
include "anim12i.mm"
include "3adant3.mm"
include "negsub.mm"
include "syl.mm"
include "eqcomd.mm"
include "breq2d.mm"
include "simp3.mm"
include "simp1.mm"
include "nn0re.mm"
include "renegcld.mm"
include "3ad2ant2.mm"
include "readdcld.mm"
include "3jca.mm"
include "cle.mm"
include "nn0negleid.mm"
include "leadd2dd.mm"
include "lelttrdi.mm"
include "sylbid.mm"

theorem difgtsumgt
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. NN0 /\ C e. RR ) -> ( C < ( A - B ) -> C < ( A + B ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cn0
    wcel
    #
    cC
    cr
    wcel
    #
    w3a
    #
    cC
    cA
    cB
    cmin
    co
    #
    clt
    wbr
    cC
    cA
    cB
    cneg
    #
    caddc
    co
    #
    clt
    wbr
    cC
    cA
    cB
    caddc
    co
    #
    clt
    wbr
    @3
    @4
    @6
    cC
    clt
    @3
    @6
    @4
    @3
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
    @6
    @4
    wceq
    @0
    @1
    @10
    @2
    @0
    @8
    @1
    @9
    cA
    recn
    cB
    nn0cn
    anim12i
    3adant3
    cA
    cB
    negsub
    syl
    eqcomd
    breq2d
    @3
    cC
    @6
    @7
    @3
    @2
    @6
    cr
    wcel
    @7
    cr
    wcel
    @0
    @1
    @2
    simp3
    @3
    cA
    @5
    @0
    @1
    @2
    simp1
    #
    @1
    @0
    @5
    cr
    wcel
    @2
    @1
    cB
    cB
    nn0re
    #
    renegcld
    3ad2ant2
    #
    readdcld
    @3
    cA
    cB
    @11
    @1
    @0
    cB
    cr
    wcel
    @2
    @12
    3ad2ant2
    #
    readdcld
    3jca
    @3
    @5
    cB
    cA
    @13
    @14
    @11
    @1
    @0
    @5
    cB
    cle
    wbr
    @2
    cB
    nn0negleid
    3ad2ant2
    leadd2dd
    lelttrdi
    sylbid
end
