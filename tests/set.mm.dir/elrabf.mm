include "crab.mm"
include "wcel.mm"
include "cvv.mm"
include "wa.mm"
include "elex.mm"
include "adantr.mm"
include "cv.mm"
include "cab.mm"
include "df-rab.mm"
include "eleq2i.mm"
include "nfel.mm"
include "nfan.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "elabgf.mm"
include "syl5bb.mm"
include "pm5.21nii.mm"

theorem elrabf
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume elrabf.1: |- F/_ x A
  assume elrabf.2: |- F/_ x B
  assume elrabf.3: |- F/ x ps
  assume elrabf.4: |- ( x = A -> ( ph <-> ps ) )


  assert |- ( A e. { x e. B | ph } <-> ( A e. B /\ ps ) )

  proof
    cA
    wph
    vx
    cB
    crab
    #
    wcel
    #
    cA
    cvv
    wcel
    #
    cA
    cB
    wcel
    #
    wps
    wa
    #
    cA
    @0
    elex
    @3
    @2
    wps
    cA
    cB
    elex
    adantr
    @1
    cA
    vx
    cv
    #
    cB
    wcel
    #
    wph
    wa
    #
    vx
    cab
    #
    wcel
    @2
    @4
    @0
    @8
    cA
    wph
    vx
    cB
    df-rab
    eleq2i
    @7
    @4
    vx
    cA
    cvv
    elrabf.1
    @3
    wps
    vx
    vx
    cA
    cB
    elrabf.1
    elrabf.2
    nfel
    elrabf.3
    nfan
    @5
    cA
    wceq
    @6
    @3
    wph
    wps
    @5
    cA
    cB
    eleq1
    elrabf.4
    anbi12d
    elabgf
    syl5bb
    pm5.21nii
end
