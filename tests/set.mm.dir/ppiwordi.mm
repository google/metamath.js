include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "cprime.mm"
include "cin.mm"
include "chash.mm"
include "cfv.mm"
include "cppi.mm"
include "cdom.mm"
include "cfn.mm"
include "wss.mm"
include "simp2.mm"
include "ppifi.mm"
include "syl.mm"
include "0red.mm"
include "0le0.mm"
include "a1i.mm"
include "simp3.mm"
include "iccss.mm"
include "syl22anc.mm"
include "ssrin.mm"
include "ssdomg.mm"
include "sylc.mm"
include "wb.mm"
include "3ad2ant1.mm"
include "hashdom.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "wceq.mm"
include "ppival.mm"
include "3brtr4d.mm"

theorem ppiwordi
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR /\ A <_ B ) -> ( ppi ` A ) <_ ( ppi ` B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    w3a
    #
    cc0
    cA
    cicc
    co
    #
    cprime
    cin
    #
    chash
    cfv
    #
    cc0
    cB
    cicc
    co
    #
    cprime
    cin
    #
    chash
    cfv
    #
    cA
    cppi
    cfv
    #
    cB
    cppi
    cfv
    #
    cle
    @3
    @6
    @9
    cle
    wbr
    #
    @5
    @8
    cdom
    wbr
    #
    @3
    @8
    cfn
    wcel
    #
    @5
    @8
    wss
    #
    @13
    @3
    @1
    @14
    @0
    @1
    @2
    simp2
    #
    cB
    ppifi
    syl
    #
    @3
    @4
    @7
    wss
    #
    @15
    @3
    cc0
    cr
    wcel
    @1
    cc0
    cc0
    cle
    wbr
    #
    @2
    @18
    @3
    0red
    @16
    @19
    @3
    0le0
    a1i
    @0
    @1
    @2
    simp3
    cc0
    cB
    cc0
    cA
    iccss
    syl22anc
    @4
    @7
    cprime
    ssrin
    syl
    @5
    @8
    cfn
    ssdomg
    sylc
    @3
    @5
    cfn
    wcel
    #
    @14
    @12
    @13
    wb
    @0
    @1
    @20
    @2
    cA
    ppifi
    3ad2ant1
    @17
    @5
    @8
    cfn
    hashdom
    syl2anc
    mpbird
    @0
    @1
    @10
    @6
    wceq
    @2
    cA
    ppival
    3ad2ant1
    @3
    @1
    @11
    @9
    wceq
    @16
    cB
    ppival
    syl
    3brtr4d
end
