include "csur.mm"
include "wcel.mm"
include "con0.mm"
include "wa.mm"
include "cv.mm"
include "c1o.mm"
include "c2o.mm"
include "cpr.mm"
include "cres.mm"
include "wf.mm"
include "wrex.mm"
include "elno.mm"
include "wi.mm"
include "cin.mm"
include "onin.mm"
include "fresin.mm"
include "feq2.mm"
include "rspcev.mm"
include "syl2an.mm"
include "an32s.mm"
include "ex.mm"
include "rexlimiva.mm"
include "imp.mm"
include "sylanb.mm"
include "sylibr.mm"

theorem noreson
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. No /\ B e. On ) -> ( A |` B ) e. No )

  proof
    cA
    csur
    wcel
    #
    cB
    con0
    wcel
    #
    wa
    vy
    cv
    #
    c1o
    c2o
    cpr
    #
    cA
    cB
    cres
    #
    wf
    #
    vy
    con0
    wrex
    #
    @4
    csur
    wcel
    @0
    vx
    cv
    #
    @3
    cA
    wf
    #
    vx
    con0
    wrex
    #
    @1
    @6
    vx
    cA
    elno
    @9
    @1
    @6
    @8
    @1
    @6
    wi
    vx
    con0
    @7
    con0
    wcel
    #
    @8
    wa
    @1
    @6
    @10
    @1
    @8
    @6
    @10
    @1
    wa
    @7
    cB
    cin
    #
    con0
    wcel
    @11
    @3
    @4
    wf
    #
    @6
    @8
    @7
    cB
    onin
    @7
    @3
    cA
    cB
    fresin
    @5
    @12
    vy
    @11
    con0
    @2
    @11
    @3
    @4
    feq2
    rspcev
    syl2an
    an32s
    ex
    rexlimiva
    imp
    sylanb
    vy
    @4
    elno
    sylibr
end
