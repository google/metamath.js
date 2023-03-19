include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wex.mm"
include "elvv.mm"
include "anbi1i.mm"
include "19.41vv.mm"
include "pm5.32i.mm"
include "2exbii.mm"
include "3bitr2ri.mm"

theorem copsex2gb
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume copsex2ga.1: |- ( A = <. x , y >. -> ( ph <-> ps ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint ph x
  disjoint ph y
  assert |- ( E. x E. y ( A = <. x , y >. /\ ps ) <-> ( A e. ( _V X. _V ) /\ ph ) )

  proof
    cA
    cvv
    cvv
    cxp
    wcel
    #
    wph
    wa
    cA
    vx
    cv
    vy
    cv
    cop
    wceq
    #
    vy
    wex
    vx
    wex
    #
    wph
    wa
    @1
    wph
    wa
    #
    vy
    wex
    vx
    wex
    @1
    wps
    wa
    #
    vy
    wex
    vx
    wex
    @0
    @2
    wph
    vx
    vy
    cA
    elvv
    anbi1i
    @1
    wph
    vx
    vy
    19.41vv
    @3
    @4
    vx
    vy
    @1
    wph
    wps
    copsex2ga.1
    pm5.32i
    2exbii
    3bitr2ri
end
