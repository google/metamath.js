include "copab.mm"
include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "elex.mm"
include "opex.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "adantr.mm"
include "exlimivv.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "2exbidv.mm"
include "df-opab.mm"
include "elab2g.mm"
include "pm5.21nii.mm"

theorem elopab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z

  disjoint A x
  disjoint A y
  disjoint x z
  disjoint A z
  disjoint y z
  disjoint ph z
  assert |- ( A e. { <. x , y >. | ph } <-> E. x E. y ( A = <. x , y >. /\ ph ) )

  proof
    cA
    wph
    vx
    vy
    copab
    #
    wcel
    cA
    cvv
    wcel
    #
    cA
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    wceq
    #
    wph
    wa
    #
    vy
    wex
    vx
    wex
    #
    cA
    @0
    elex
    @6
    @1
    vx
    vy
    @5
    @1
    wph
    @5
    @1
    @4
    cvv
    wcel
    @2
    @3
    opex
    cA
    @4
    cvv
    eleq1
    mpbiri
    adantr
    exlimivv
    vz
    cv
    #
    @4
    wceq
    #
    wph
    wa
    #
    vy
    wex
    vx
    wex
    @7
    vz
    cA
    @0
    cvv
    @8
    cA
    wceq
    #
    @10
    @6
    vx
    vy
    @11
    @9
    @5
    wph
    @8
    cA
    @4
    eqeq1
    anbi1d
    2exbidv
    wph
    vx
    vy
    vz
    df-opab
    elab2g
    pm5.21nii
end
