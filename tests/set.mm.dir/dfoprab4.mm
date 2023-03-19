include "cv.mm"
include "cxp.mm"
include "wcel.mm"
include "wa.mm"
include "copab.mm"
include "cvv.mm"
include "coprab.mm"
include "xpss.mm"
include "sseli.mm"
include "adantr.mm"
include "pm4.71ri.mm"
include "opabbii.mm"
include "cop.mm"
include "wceq.mm"
include "eleq1.mm"
include "opelxp.mm"
include "syl6bb.mm"
include "anbi12d.mm"
include "dfoprab3.mm"
include "eqtri.mm"

theorem dfoprab4
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  assume dfoprab4.1: |- ( w = <. x , y >. -> ( ph <-> ps ) )

  disjoint w x
  disjoint w y
  disjoint A w
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  disjoint ps w
  disjoint w z
  disjoint x z
  disjoint y z
  assert |- { <. w , z >. | ( w e. ( A X. B ) /\ ph ) } = { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ ps ) }

  proof
    vw
    cv
    #
    cA
    cB
    cxp
    #
    wcel
    #
    wph
    wa
    #
    vw
    vz
    copab
    @0
    cvv
    cvv
    cxp
    #
    wcel
    #
    @3
    wa
    #
    vw
    vz
    copab
    vx
    cv
    #
    cA
    wcel
    vy
    cv
    #
    cB
    wcel
    wa
    #
    wps
    wa
    #
    vx
    vy
    vz
    coprab
    @3
    @6
    vw
    vz
    @3
    @5
    @2
    @5
    wph
    @1
    @4
    @0
    cA
    cB
    xpss
    sseli
    adantr
    pm4.71ri
    opabbii
    @3
    @10
    vx
    vy
    vz
    vw
    @0
    @7
    @8
    cop
    #
    wceq
    #
    @2
    @9
    wph
    wps
    @12
    @2
    @11
    @1
    wcel
    @9
    @0
    @11
    @1
    eleq1
    @7
    @8
    cA
    cB
    opelxp
    syl6bb
    dfoprab4.1
    anbi12d
    dfoprab3
    eqtri
end
