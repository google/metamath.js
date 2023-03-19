include "cwlim.mm"
include "wcel.mm"
include "cinf.mm"
include "wne.mm"
include "cpred.mm"
include "csup.mm"
include "wceq.mm"
include "wa.mm"
include "w3a.mm"
include "cv.mm"
include "neeq1.mm"
include "id.mm"
include "predeq3.mm"
include "supeq1d.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "df-wlim.mm"
include "elrab2.mm"
include "3anass.mm"
include "bitr4i.mm"

theorem elwlim
  let cA: class A
  let cR: class R
  let cX: class X
  let vx: setvar x


  assert |- ( X e. WLim ( R , A ) <-> ( X e. A /\ X =/= inf ( A , A , R ) /\ X = sup ( Pred ( R , A , X ) , A , R ) ) )

  proof
    cX
    cA
    cR
    cwlim
    #
    wcel
    cX
    cA
    wcel
    #
    cX
    cA
    cA
    cR
    cinf
    #
    wne
    #
    cX
    cA
    cR
    cX
    cpred
    #
    cA
    cR
    csup
    #
    wceq
    #
    wa
    #
    wa
    @1
    @3
    @6
    w3a
    vx
    cv
    #
    @2
    wne
    #
    @8
    cA
    cR
    @8
    cpred
    #
    cA
    cR
    csup
    #
    wceq
    #
    wa
    @7
    vx
    cX
    cA
    @0
    @8
    cX
    wceq
    #
    @9
    @3
    @12
    @6
    @8
    cX
    @2
    neeq1
    @13
    @8
    cX
    @11
    @5
    @13
    id
    @13
    cA
    @10
    @4
    cR
    cA
    cR
    @8
    cX
    predeq3
    supeq1d
    eqeq12d
    anbi12d
    vx
    cA
    cR
    df-wlim
    elrab2
    @1
    @3
    @6
    3anass
    bitr4i
end
