include "cfn.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "cdom.mm"
include "ssdomg.mm"
include "com12.mm"
include "adantl.mm"
include "impcom.mm"
include "wb.mm"
include "ssfi.mm"
include "adantrl.mm"
include "simpl.mm"
include "hashdom.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "ex.mm"
include "wn.mm"
include "cpnf.mm"
include "wceq.mm"
include "hashinf.mm"
include "cvv.mm"
include "cxr.mm"
include "ssexg.mm"
include "ancoms.mm"
include "hashxrcl.mm"
include "pnfge.mm"
include "3syl.mm"
include "breq2.mm"
include "adantr.mm"
include "sylibrd.mm"
include "expcom.mm"
include "mpd.mm"
include "impancom.mm"
include "pm2.61i.mm"

theorem hashss
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( ( A e. V /\ B C_ A ) -> ( # ` B ) <_ ( # ` A ) )

  proof
    cA
    cfn
    wcel
    #
    cA
    cV
    wcel
    #
    cB
    cA
    wss
    #
    wa
    #
    cB
    chash
    cfv
    #
    cA
    chash
    cfv
    #
    cle
    wbr
    #
    wi
    @0
    @3
    @6
    @0
    @3
    wa
    #
    @6
    cB
    cA
    cdom
    wbr
    #
    @3
    @0
    @8
    @2
    @0
    @8
    wi
    @1
    @0
    @2
    @8
    cB
    cA
    cfn
    ssdomg
    com12
    adantl
    impcom
    @7
    cB
    cfn
    wcel
    #
    @0
    @6
    @8
    wb
    @0
    @2
    @9
    @1
    cA
    cB
    ssfi
    adantrl
    @0
    @3
    simpl
    cB
    cA
    cfn
    hashdom
    syl2anc
    mpbird
    ex
    @3
    @0
    wn
    #
    @6
    @1
    @10
    @2
    @6
    @1
    @10
    wa
    @5
    cpnf
    wceq
    #
    @2
    @6
    wi
    #
    cA
    cV
    hashinf
    @1
    @11
    @12
    wi
    @10
    @11
    @1
    @12
    @11
    @1
    wa
    @2
    @4
    cpnf
    cle
    wbr
    #
    @6
    @1
    @2
    @13
    wi
    @11
    @1
    @2
    @13
    @3
    cB
    cvv
    wcel
    #
    @4
    cxr
    wcel
    @13
    @2
    @1
    @14
    cB
    cA
    cV
    ssexg
    ancoms
    cB
    cvv
    hashxrcl
    @4
    pnfge
    3syl
    ex
    adantl
    @11
    @6
    @13
    wb
    @1
    @5
    cpnf
    @4
    cle
    breq2
    adantr
    sylibrd
    expcom
    adantr
    mpd
    impancom
    com12
    pm2.61i
end
