include "con0.mm"
include "wss.mm"
include "word.mm"
include "cv.mm"
include "cale.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wsmo.mm"
include "ssid.mm"
include "ordon.mm"
include "alephord2i.mm"
include "ralrimiv.mm"
include "rgen.mm"
include "wf.mm"
include "w3a.mm"
include "wi.mm"
include "wfn.mm"
include "crn.mm"
include "alephfnon.mm"
include "alephsson.mm"
include "df-f.mm"
include "mpbir2an.mm"
include "issmo2.mm"
include "ax-mp.mm"
include "mp3an.mm"

theorem alephsmo
  let vx: setvar x
  let vy: setvar y


  assert |- Smo aleph

  proof
    con0
    con0
    wss
    #
    con0
    word
    #
    vy
    cv
    #
    cale
    cfv
    vx
    cv
    #
    cale
    cfv
    wcel
    #
    vy
    @3
    wral
    #
    vx
    con0
    wral
    #
    cale
    wsmo
    #
    con0
    ssid
    ordon
    @5
    vx
    con0
    @3
    con0
    wcel
    @4
    vy
    @3
    @2
    @3
    alephord2i
    ralrimiv
    rgen
    con0
    con0
    cale
    wf
    #
    @0
    @1
    @6
    w3a
    @7
    wi
    @8
    cale
    con0
    wfn
    cale
    crn
    con0
    wss
    alephfnon
    alephsson
    con0
    con0
    cale
    df-f
    mpbir2an
    vx
    vy
    con0
    con0
    cale
    issmo2
    ax-mp
    mp3an
end
