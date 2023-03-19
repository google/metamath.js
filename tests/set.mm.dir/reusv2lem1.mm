include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wceq.mm"
include "wral.mm"
include "wmo.mm"
include "weu.mm"
include "wex.mm"
include "wb.mm"
include "wcel.mm"
include "n0.mm"
include "nfra1.mm"
include "nfmo.mm"
include "wi.mm"
include "wal.mm"
include "rsp.mm"
include "com12.mm"
include "alrimiv.mm"
include "mo2icl.mm"
include "syl.mm"
include "exlimi.mm"
include "sylbi.mm"
include "eu5.mm"
include "rbaib.mm"

theorem reusv2lem1
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  let cC: class C
  let wph: wff ph

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C x
  disjoint C z
  disjoint ph x
  disjoint ph z
  assert |- ( A =/= (/) -> ( E! x A. y e. A x = B <-> E. x A. y e. A x = B ) )

  proof
    cA
    c0
    wne
    #
    vx
    cv
    cB
    wceq
    #
    vy
    cA
    wral
    #
    vx
    wmo
    #
    @2
    vx
    weu
    #
    @2
    vx
    wex
    #
    wb
    @0
    vy
    cv
    cA
    wcel
    #
    vy
    wex
    @3
    vy
    cA
    n0
    @6
    @3
    vy
    @2
    vy
    vx
    @1
    vy
    cA
    nfra1
    nfmo
    @6
    @2
    @1
    wi
    #
    vx
    wal
    @3
    @6
    @7
    vx
    @2
    @6
    @1
    @1
    vy
    cA
    rsp
    com12
    alrimiv
    @2
    vx
    cB
    mo2icl
    syl
    exlimi
    sylbi
    @4
    @5
    @3
    @2
    vx
    eu5
    rbaib
    syl
end
