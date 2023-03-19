include "cdif.mm"
include "wcel.mm"
include "cvv.mm"
include "wn.mm"
include "wa.mm"
include "elex.mm"
include "adantr.mm"
include "cv.mm"
include "wceq.mm"
include "eleq1.mm"
include "notbid.mm"
include "anbi12d.mm"
include "df-dif.mm"
include "elab2g.mm"
include "pm5.21nii.mm"

theorem eldif
  param cA: class A
  param cB: class B
  param cC: class C
  let vx: setvar x


  assert |- ( A e. ( B \ C ) <-> ( A e. B /\ -. A e. C ) )

  proof
    cA
    cB
    cC
    cdif
    #
    wcel
    cA
    cvv
    wcel
    #
    cA
    cB
    wcel
    #
    cA
    cC
    wcel
    #
    wn
    #
    wa
    #
    cA
    @0
    elex
    @2
    @1
    @4
    cA
    cB
    elex
    adantr
    vx
    cv
    #
    cB
    wcel
    #
    @6
    cC
    wcel
    #
    wn
    #
    wa
    @5
    vx
    cA
    @0
    cvv
    @6
    cA
    wceq
    #
    @7
    @2
    @9
    @4
    @6
    cA
    cB
    eleq1
    @10
    @8
    @3
    @6
    cA
    cC
    eleq1
    notbid
    anbi12d
    vx
    cB
    cC
    df-dif
    elab2g
    pm5.21nii
end
