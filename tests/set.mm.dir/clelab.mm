include "cab.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "df-clel.mm"
include "nfv.mm"
include "nfsab1.mm"
include "nfan.mm"
include "weq.mm"
include "eqeq1.mm"
include "wsb.mm"
include "sbequ12.mm"
include "df-clab.mm"
include "syl6bbr.mm"
include "anbi12d.mm"
include "cbvex.mm"
include "bitr4i.mm"

theorem clelab
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint ph y
  assert |- ( A e. { x | ph } <-> E. x ( x = A /\ ph ) )

  proof
    cA
    wph
    vx
    cab
    #
    wcel
    vy
    cv
    #
    cA
    wceq
    #
    @1
    @0
    wcel
    #
    wa
    #
    vy
    wex
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
    vy
    cA
    @0
    df-clel
    @7
    @4
    vx
    vy
    @7
    vy
    nfv
    @2
    @3
    vx
    @2
    vx
    nfv
    wph
    vx
    vy
    nfsab1
    nfan
    vx
    vy
    weq
    #
    @6
    @2
    wph
    @3
    @5
    @1
    cA
    eqeq1
    @8
    wph
    wph
    vx
    vy
    wsb
    @3
    wph
    vx
    vy
    sbequ12
    wph
    vy
    vx
    df-clab
    syl6bbr
    anbi12d
    cbvex
    bitr4i
end
