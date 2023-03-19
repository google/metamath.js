include "cid.mm"
include "cres.mm"
include "con0.mm"
include "wf.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "fnresi.mm"
include "rnresi.mm"
include "word.mm"
include "ordsson.mm"
include "ax-mp.mm"
include "eqsstri.mm"
include "df-f.mm"
include "mpbir2an.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "fvresi.mm"
include "adantr.mm"
include "adantl.mm"
include "eleq12d.mm"
include "biimprd.mm"
include "dmresi.mm"
include "issmo.mm"

theorem iordsmo
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  assume iordsmo.1: |- Ord A


  assert |- Smo ( _I |` A )

  proof
    vx
    vy
    cid
    cA
    cres
    #
    cA
    cA
    con0
    @0
    wf
    @0
    cA
    wfn
    @0
    crn
    #
    con0
    wss
    cA
    fnresi
    @1
    cA
    con0
    cA
    rnresi
    cA
    word
    cA
    con0
    wss
    iordsmo.1
    cA
    ordsson
    ax-mp
    eqsstri
    cA
    con0
    @0
    df-f
    mpbir2an
    iordsmo.1
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cA
    wcel
    #
    wa
    #
    @2
    @0
    cfv
    #
    @4
    @0
    cfv
    #
    wcel
    @2
    @4
    wcel
    @6
    @7
    @2
    @8
    @4
    @3
    @7
    @2
    wceq
    @5
    cA
    @2
    fvresi
    adantr
    @5
    @8
    @4
    wceq
    @3
    cA
    @4
    fvresi
    adantl
    eleq12d
    biimprd
    cA
    dmresi
    issmo
end
