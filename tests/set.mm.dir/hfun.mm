include "chf.mm"
include "wcel.mm"
include "wa.mm"
include "cun.mm"
include "crnk.mm"
include "cfv.mm"
include "com.mm"
include "rankung.mm"
include "elhf2g.mm"
include "ibi.mm"
include "wceq.mm"
include "wi.mm"
include "eleq1a.mm"
include "adantl.mm"
include "uncom.mm"
include "eqeq1i.mm"
include "biimpi.mm"
include "eleq1d.mm"
include "biimprcd.mm"
include "adantr.mm"
include "wss.mm"
include "wo.mm"
include "word.mm"
include "nnord.mm"
include "ordtri2or2.mm"
include "syl2an.mm"
include "ssequn1.mm"
include "orbi12i.mm"
include "sylib.mm"
include "mpjaod.mm"
include "eqeltrd.mm"
include "cvv.mm"
include "wb.mm"
include "unexg.mm"
include "syl.mm"
include "mpbird.mm"

theorem hfun
  let cA: class A
  let cB: class B


  assert |- ( ( A e. Hf /\ B e. Hf ) -> ( A u. B ) e. Hf )

  proof
    cA
    chf
    wcel
    #
    cB
    chf
    wcel
    #
    wa
    #
    cA
    cB
    cun
    #
    chf
    wcel
    #
    @3
    crnk
    cfv
    #
    com
    wcel
    #
    @2
    @5
    cA
    crnk
    cfv
    #
    cB
    crnk
    cfv
    #
    cun
    #
    com
    cA
    cB
    chf
    chf
    rankung
    @0
    @7
    com
    wcel
    #
    @8
    com
    wcel
    #
    @9
    com
    wcel
    #
    @1
    @0
    @10
    cA
    chf
    elhf2g
    ibi
    @1
    @11
    cB
    chf
    elhf2g
    ibi
    @10
    @11
    wa
    #
    @9
    @8
    wceq
    #
    @12
    @8
    @7
    cun
    #
    @7
    wceq
    #
    @11
    @14
    @12
    wi
    @10
    @8
    com
    @9
    eleq1a
    adantl
    @10
    @16
    @12
    wi
    @11
    @16
    @12
    @10
    @16
    @9
    @7
    com
    @16
    @9
    @7
    wceq
    @15
    @9
    @7
    @8
    @7
    uncom
    eqeq1i
    biimpi
    eleq1d
    biimprcd
    adantr
    @13
    @7
    @8
    wss
    #
    @8
    @7
    wss
    #
    wo
    #
    @14
    @16
    wo
    @10
    @7
    word
    @8
    word
    @19
    @11
    @7
    nnord
    @8
    nnord
    @7
    @8
    ordtri2or2
    syl2an
    @17
    @14
    @18
    @16
    @7
    @8
    ssequn1
    @8
    @7
    ssequn1
    orbi12i
    sylib
    mpjaod
    syl2an
    eqeltrd
    @2
    @3
    cvv
    wcel
    @4
    @6
    wb
    cA
    cB
    chf
    chf
    unexg
    @3
    cvv
    elhf2g
    syl
    mpbird
end
