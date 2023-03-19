include "cab.mm"
include "cuni.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "wex.mm"
include "eluni.mm"
include "nfv.mm"
include "nfsab1.mm"
include "nfan.mm"
include "weq.mm"
include "eleq2.mm"
include "eleq1.mm"
include "abid.mm"
include "syl6bb.mm"
include "anbi12d.mm"
include "cbvex.mm"
include "bitri.mm"

theorem eluniab
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint ph y
  assert |- ( A e. U. { x | ph } <-> E. x ( A e. x /\ ph ) )

  proof
    cA
    wph
    vx
    cab
    #
    cuni
    wcel
    cA
    vy
    cv
    #
    wcel
    #
    @1
    @0
    wcel
    #
    wa
    #
    vy
    wex
    cA
    vx
    cv
    #
    wcel
    #
    wph
    wa
    #
    vx
    wex
    vy
    cA
    @0
    eluni
    @4
    @7
    vy
    vx
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
    @7
    vy
    nfv
    vy
    vx
    weq
    #
    @2
    @6
    @3
    wph
    @1
    @5
    cA
    eleq2
    @8
    @3
    @5
    @0
    wcel
    wph
    @1
    @5
    @0
    eleq1
    wph
    vx
    abid
    syl6bb
    anbi12d
    cbvex
    bitri
end
