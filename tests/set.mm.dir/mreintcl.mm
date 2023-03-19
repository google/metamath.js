include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cpw.mm"
include "cv.mm"
include "cint.mm"
include "wi.mm"
include "wral.mm"
include "elpw2g.mm"
include "biimpar.mm"
include "3adant3.mm"
include "ismre.mm"
include "simp3bi.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "wceq.mm"
include "neeq1.mm"
include "inteq.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "3impia.mm"
include "syl3anc.mm"

theorem mreintcl
  let cC: class C
  let cS: class S
  let cX: class X
  let vc: setvar c
  let vs: setvar s
  let vx: setvar x


  assert |- ( ( C e. ( Moore ` X ) /\ S C_ C /\ S =/= (/) ) -> |^| S e. C )

  proof
    cC
    cX
    cmre
    cfv
    #
    wcel
    #
    cS
    cC
    wss
    #
    cS
    c0
    wne
    #
    w3a
    cS
    cC
    cpw
    #
    wcel
    #
    vs
    cv
    #
    c0
    wne
    #
    @6
    cint
    #
    cC
    wcel
    #
    wi
    #
    vs
    @4
    wral
    #
    @3
    cS
    cint
    #
    cC
    wcel
    #
    @1
    @2
    @5
    @3
    @1
    @5
    @2
    cS
    cC
    @0
    elpw2g
    biimpar
    3adant3
    @1
    @2
    @11
    @3
    @1
    cC
    cX
    cpw
    wss
    cX
    cC
    wcel
    @11
    cC
    cX
    vs
    ismre
    simp3bi
    3ad2ant1
    @1
    @2
    @3
    simp3
    @5
    @11
    @3
    @13
    @10
    @3
    @13
    wi
    vs
    cS
    @4
    @6
    cS
    wceq
    #
    @7
    @3
    @9
    @13
    @6
    cS
    c0
    neeq1
    @14
    @8
    @12
    cC
    @6
    cS
    inteq
    eleq1d
    imbi12d
    rspcva
    3impia
    syl3anc
end
