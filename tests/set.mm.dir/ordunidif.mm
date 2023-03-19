include "word.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wss.mm"
include "cdif.mm"
include "wrex.mm"
include "wral.mm"
include "cuni.mm"
include "wceq.mm"
include "wi.mm"
include "con0.mm"
include "ordelon.mm"
include "onelss.mm"
include "syl.mm"
include "wn.mm"
include "eloni.mm"
include "ordirr.mm"
include "eldif.mm"
include "simplbi2.mm"
include "syl5.mm"
include "adantl.mm"
include "mpd.mm"
include "jctild.mm"
include "adantr.mm"
include "sseq2.mm"
include "rspcev.mm"
include "syl6.mm"
include "biimpri.mm"
include "ssid.mm"
include "jctir.mm"
include "ex.mm"
include "pm2.61d.mm"
include "ralrimiva.mm"
include "unidif.mm"

theorem ordunidif
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( Ord A /\ B e. A ) -> U. ( A \ B ) = U. A )

  proof
    cA
    word
    #
    cB
    cA
    wcel
    #
    wa
    #
    vx
    cv
    #
    vy
    cv
    #
    wss
    #
    vy
    cA
    cB
    cdif
    #
    wrex
    #
    vx
    cA
    wral
    @6
    cuni
    cA
    cuni
    wceq
    @2
    @7
    vx
    cA
    @2
    @3
    cA
    wcel
    #
    wa
    #
    @3
    cB
    wcel
    #
    @7
    @9
    @10
    cB
    @6
    wcel
    #
    @3
    cB
    wss
    #
    wa
    #
    @7
    @2
    @10
    @13
    wi
    @8
    @2
    @10
    @12
    @11
    @2
    cB
    con0
    wcel
    #
    @10
    @12
    wi
    cA
    cB
    ordelon
    #
    cB
    @3
    onelss
    syl
    @2
    @14
    @11
    @15
    @1
    @14
    @11
    wi
    @0
    @14
    cB
    cB
    wcel
    wn
    #
    @1
    @11
    @14
    cB
    word
    @16
    cB
    eloni
    cB
    ordirr
    syl
    @11
    @1
    @16
    cB
    cA
    cB
    eldif
    simplbi2
    syl5
    adantl
    mpd
    jctild
    adantr
    @5
    @12
    vy
    cB
    @6
    @4
    cB
    @3
    sseq2
    rspcev
    syl6
    @8
    @10
    wn
    #
    @7
    wi
    @2
    @8
    @17
    @3
    @6
    wcel
    #
    @3
    @3
    wss
    #
    wa
    #
    @7
    @8
    @17
    @20
    @8
    @17
    wa
    #
    @18
    @19
    @18
    @21
    @3
    cA
    cB
    eldif
    biimpri
    @3
    ssid
    jctir
    ex
    @5
    @19
    vy
    @3
    @6
    @4
    @3
    @3
    sseq2
    rspcev
    syl6
    adantl
    pm2.61d
    ralrimiva
    vx
    vy
    cA
    cB
    unidif
    syl
end
