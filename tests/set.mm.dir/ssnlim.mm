include "word.mm"
include "cv.mm"
include "wlim.mm"
include "wn.mm"
include "con0.mm"
include "crab.mm"
include "wss.mm"
include "wa.mm"
include "com.mm"
include "wcel.mm"
include "limom.mm"
include "ssel.mm"
include "wceq.mm"
include "limeq.mm"
include "notbid.mm"
include "elrab.mm"
include "simprbi.mm"
include "syl6.mm"
include "mt2i.mm"
include "adantl.mm"
include "wb.mm"
include "ordom.mm"
include "ordtri1.mm"
include "mpan2.mm"
include "adantr.mm"
include "mpbird.mm"

theorem ssnlim
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( ( Ord A /\ A C_ { x e. On | -. Lim x } ) -> A C_ _om )

  proof
    cA
    word
    #
    cA
    vx
    cv
    #
    wlim
    #
    wn
    #
    vx
    con0
    crab
    #
    wss
    #
    wa
    cA
    com
    wss
    #
    com
    cA
    wcel
    #
    wn
    #
    @5
    @8
    @0
    @5
    @7
    com
    wlim
    #
    limom
    @5
    @7
    com
    @4
    wcel
    #
    @9
    wn
    #
    cA
    @4
    com
    ssel
    @10
    com
    con0
    wcel
    @11
    @3
    @11
    vx
    com
    con0
    @1
    com
    wceq
    @2
    @9
    @1
    com
    limeq
    notbid
    elrab
    simprbi
    syl6
    mt2i
    adantl
    @0
    @6
    @8
    wb
    #
    @5
    @0
    com
    word
    @12
    ordom
    cA
    com
    ordtri1
    mpan2
    adantr
    mpbird
end
