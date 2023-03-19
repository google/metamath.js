include "com.mm"
include "word.mm"
include "wlim.mm"
include "ordom.mm"
include "con0.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "ordeleqon.mm"
include "cv.mm"
include "wi.mm"
include "wal.mm"
include "wn.mm"
include "ordirr.mm"
include "ax-mp.mm"
include "elom.mm"
include "baib.mm"
include "mtbii.mm"
include "wss.mm"
include "limomss.mm"
include "wb.mm"
include "limord.mm"
include "ordsseleq.mm"
include "sylancr.mm"
include "mpbid.mm"
include "ord.mm"
include "limeq.mm"
include "biimprcd.mm"
include "syld.mm"
include "con1d.mm"
include "com12.mm"
include "alrimiv.mm"
include "nsyl2.mm"
include "limon.mm"
include "mpbiri.mm"
include "jaoi.mm"
include "sylbi.mm"

theorem limom
  let vx: setvar x


  assert |- Lim _om

  proof
    com
    word
    #
    com
    wlim
    #
    ordom
    @0
    com
    con0
    wcel
    #
    com
    con0
    wceq
    #
    wo
    @1
    com
    ordeleqon
    @2
    @1
    @3
    @2
    vx
    cv
    #
    wlim
    #
    com
    @4
    wcel
    #
    wi
    #
    vx
    wal
    #
    @1
    @2
    com
    com
    wcel
    #
    @8
    @0
    @9
    wn
    ordom
    com
    ordirr
    ax-mp
    @9
    @2
    @8
    vx
    com
    elom
    baib
    mtbii
    @1
    wn
    #
    @7
    vx
    @5
    @10
    @6
    @5
    @6
    @1
    @5
    @6
    wn
    com
    @4
    wceq
    #
    @1
    @5
    @6
    @11
    @5
    com
    @4
    wss
    #
    @6
    @11
    wo
    #
    @4
    limomss
    @5
    @0
    @4
    word
    @12
    @13
    wb
    ordom
    @4
    limord
    com
    @4
    ordsseleq
    sylancr
    mpbid
    ord
    @11
    @1
    @5
    com
    @4
    limeq
    biimprcd
    syld
    con1d
    com12
    alrimiv
    nsyl2
    @3
    @1
    con0
    wlim
    limon
    com
    con0
    limeq
    mpbiri
    jaoi
    sylbi
    ax-mp
end
