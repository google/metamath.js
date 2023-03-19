include "con0.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wceq.mm"
include "cdif.mm"
include "cin.mm"
include "c0.mm"
include "wrex.mm"
include "wn.mm"
include "eldifn.mm"
include "adantl.mm"
include "eldifi.mm"
include "onss.mm"
include "difin0ss.mm"
include "syl5com.mm"
include "imim1d.mm"
include "a2i.mm"
include "syl5.mm"
include "imp.mm"
include "mtod.mm"
include "ex.mm"
include "ralimi2.mm"
include "ralnex.mm"
include "sylib.mm"
include "wne.mm"
include "ssdif0.mm"
include "necon3bbii.mm"
include "word.mm"
include "ordon.mm"
include "difss.mm"
include "tz7.5.mm"
include "mp3an12.mm"
include "sylbi.mm"
include "nsyl2.mm"
include "anim2i.mm"
include "eqss.mm"
include "sylibr.mm"

theorem tfi
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( ( A C_ On /\ A. x e. On ( x C_ A -> x e. A ) ) -> A = On )

  proof
    cA
    con0
    wss
    #
    vx
    cv
    #
    cA
    wss
    #
    @1
    cA
    wcel
    #
    wi
    #
    vx
    con0
    wral
    #
    wa
    @0
    con0
    cA
    wss
    #
    wa
    cA
    con0
    wceq
    @5
    @6
    @0
    @5
    con0
    cA
    cdif
    #
    @1
    cin
    c0
    wceq
    #
    vx
    @7
    wrex
    #
    @6
    @5
    @8
    wn
    #
    vx
    @7
    wral
    @9
    wn
    @4
    @10
    vx
    con0
    @7
    @1
    con0
    wcel
    #
    @4
    wi
    #
    @1
    @7
    wcel
    #
    @10
    @12
    @13
    wa
    @8
    @3
    @13
    @3
    wn
    @12
    @1
    con0
    cA
    eldifn
    adantl
    @12
    @13
    @8
    @3
    wi
    #
    @13
    @11
    @12
    @14
    @1
    con0
    cA
    eldifi
    @11
    @4
    @14
    @11
    @8
    @2
    @3
    @11
    @1
    con0
    wss
    @8
    @2
    @1
    onss
    con0
    cA
    @1
    difin0ss
    syl5com
    imim1d
    a2i
    syl5
    imp
    mtod
    ex
    ralimi2
    @8
    vx
    @7
    ralnex
    sylib
    @6
    wn
    @7
    c0
    wne
    #
    @9
    @6
    @7
    c0
    con0
    cA
    ssdif0
    necon3bbii
    con0
    word
    @7
    con0
    wss
    @15
    @9
    ordon
    con0
    cA
    difss
    vx
    con0
    @7
    tz7.5
    mp3an12
    sylbi
    nsyl2
    anim2i
    cA
    con0
    eqss
    sylibr
end
