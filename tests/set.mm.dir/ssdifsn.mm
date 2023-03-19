include "csn.mm"
include "cdif.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "wne.mm"
include "wa.mm"
include "wn.mm"
include "dfss3.mm"
include "eldifsn.mm"
include "ralbii.mm"
include "bitri.mm"
include "r19.26.mm"
include "bicomi.mm"
include "neirr.mm"
include "neeq1.mm"
include "rspccv.mm"
include "mtoi.mm"
include "nelelne.mm"
include "ralrimiv.mm"
include "impbii.mm"
include "anbi12i.mm"

theorem ssdifsn
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A C_ ( B \ { C } ) <-> ( A C_ B /\ -. C e. A ) )

  proof
    cA
    cB
    cC
    csn
    cdif
    #
    wss
    #
    vx
    cv
    #
    cB
    wcel
    #
    vx
    cA
    wral
    #
    @2
    cC
    wne
    #
    vx
    cA
    wral
    #
    wa
    #
    cA
    cB
    wss
    #
    cC
    cA
    wcel
    #
    wn
    #
    wa
    @1
    @3
    @5
    wa
    #
    vx
    cA
    wral
    #
    @7
    @1
    @2
    @0
    wcel
    #
    vx
    cA
    wral
    @12
    vx
    cA
    @0
    dfss3
    @13
    @11
    vx
    cA
    @2
    cB
    cC
    eldifsn
    ralbii
    bitri
    @3
    @5
    vx
    cA
    r19.26
    bitri
    @4
    @8
    @6
    @10
    @8
    @4
    vx
    cA
    cB
    dfss3
    bicomi
    @6
    @10
    @6
    @9
    cC
    cC
    wne
    #
    cC
    neirr
    @5
    @14
    vx
    cC
    cA
    @2
    cC
    cC
    neeq1
    rspccv
    mtoi
    @10
    @5
    vx
    cA
    cC
    cA
    @2
    nelelne
    ralrimiv
    impbii
    anbi12i
    bitri
end
