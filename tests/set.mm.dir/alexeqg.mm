include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "eqeq2.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "imbi1d.mm"
include "albidv.mm"
include "sb56.mm"
include "vtoclbg.mm"
include "bicomd.mm"

theorem alexeqg
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint ph y
  assert |- ( A e. V -> ( A. x ( x = A -> ph ) <-> E. x ( x = A /\ ph ) ) )

  proof
    cA
    cV
    wcel
    vx
    cv
    #
    cA
    wceq
    #
    wph
    wa
    #
    vx
    wex
    #
    @1
    wph
    wi
    #
    vx
    wal
    #
    @0
    vy
    cv
    #
    wceq
    #
    wph
    wa
    #
    vx
    wex
    @7
    wph
    wi
    #
    vx
    wal
    @3
    @5
    vy
    cA
    cV
    @6
    cA
    wceq
    #
    @8
    @2
    vx
    @10
    @7
    @1
    wph
    @6
    cA
    @0
    eqeq2
    #
    anbi1d
    exbidv
    @10
    @9
    @4
    vx
    @10
    @7
    @1
    wph
    @11
    imbi1d
    albidv
    wph
    vx
    vy
    sb56
    vtoclbg
    bicomd
end
