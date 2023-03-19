include "wor.mm"
include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "wn.mm"
include "wa.mm"
include "fiming.mm"
include "weq.mm"
include "equcom.mm"
include "wb.mm"
include "sotrieq2.mm"
include "ancom2s.mm"
include "syl5bb.mm"
include "simprbda.mm"
include "ex.mm"
include "anassrs.mm"
include "a1dd.mm"
include "pm2.27.mm"
include "so2nr.mm"
include "pm3.21.mm"
include "con3d.mm"
include "syl5com.mm"
include "syl9r.mm"
include "pm2.61dne.mm"
include "ralimdva.mm"
include "breq1.mm"
include "rspcev.mm"
include "ralrimivw.mm"
include "adantl.mm"
include "jctird.mm"
include "reximdva.mm"
include "3ad2ant1.mm"
include "mpd.mm"

theorem fiinfg
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cR: class R

  disjoint R x
  disjoint R y
  disjoint R z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A x
  disjoint A y
  disjoint A z
  assert |- ( ( R Or A /\ A e. Fin /\ A =/= (/) ) -> E. x e. A ( A. y e. A -. y R x /\ A. y e. A ( x R y -> E. z e. A z R y ) ) )

  proof
    cA
    cR
    wor
    #
    cA
    cfn
    wcel
    #
    cA
    c0
    wne
    #
    w3a
    vx
    cv
    #
    vy
    cv
    #
    wne
    #
    @3
    @4
    cR
    wbr
    #
    wi
    #
    vy
    cA
    wral
    #
    vx
    cA
    wrex
    #
    @4
    @3
    cR
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    @6
    vz
    cv
    #
    @4
    cR
    wbr
    #
    vz
    cA
    wrex
    #
    wi
    #
    vy
    cA
    wral
    #
    wa
    #
    vx
    cA
    wrex
    #
    vx
    vy
    cA
    cR
    fiming
    @0
    @1
    @9
    @19
    wi
    @2
    @0
    @8
    @18
    vx
    cA
    @0
    @3
    cA
    wcel
    #
    wa
    #
    @8
    @12
    @17
    @21
    @7
    @11
    vy
    cA
    @21
    @4
    cA
    wcel
    #
    wa
    #
    @7
    @11
    wi
    @3
    @4
    @23
    vx
    vy
    weq
    #
    @11
    @7
    @0
    @20
    @22
    @24
    @11
    wi
    @0
    @20
    @22
    wa
    wa
    #
    @24
    @11
    @25
    @24
    @11
    @6
    wn
    #
    @24
    vy
    vx
    weq
    #
    @25
    @11
    @26
    wa
    #
    vx
    vy
    equcom
    @0
    @22
    @20
    @27
    @28
    wb
    cA
    @4
    @3
    cR
    sotrieq2
    ancom2s
    syl5bb
    simprbda
    ex
    anassrs
    a1dd
    @5
    @7
    @6
    @23
    @11
    @5
    @6
    pm2.27
    @0
    @20
    @22
    @6
    @11
    wi
    @25
    @10
    @6
    wa
    #
    wn
    #
    @6
    @11
    @0
    @22
    @20
    @30
    cA
    @4
    @3
    cR
    so2nr
    ancom2s
    @6
    @10
    @29
    @6
    @10
    pm3.21
    con3d
    syl5com
    anassrs
    syl9r
    pm2.61dne
    ralimdva
    @20
    @17
    @0
    @20
    @16
    vy
    cA
    @20
    @6
    @15
    @14
    @6
    vz
    @3
    cA
    @13
    @3
    @4
    cR
    breq1
    rspcev
    ex
    ralrimivw
    adantl
    jctird
    reximdva
    3ad2ant1
    mpd
end
