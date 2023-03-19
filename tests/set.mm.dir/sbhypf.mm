include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "wsb.mm"
include "wb.mm"
include "eqeq1.mm"
include "equsexvw.mm"
include "nfs1v.mm"
include "nfbi.mm"
include "sbequ12.mm"
include "bicomd.mm"
include "sylan9bb.mm"
include "exlimi.mm"
include "sylbir.mm"

theorem sbhypf
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume sbhypf.1: |- F/ x ps
  assume sbhypf.2: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  disjoint x y
  assert |- ( y = A -> ( [ y / x ] ph <-> ps ) )

  proof
    vy
    cv
    #
    cA
    wceq
    #
    vx
    cv
    #
    @0
    wceq
    #
    @2
    cA
    wceq
    #
    wa
    #
    vx
    wex
    wph
    vx
    vy
    wsb
    #
    wps
    wb
    #
    @4
    @1
    vx
    vy
    @2
    @0
    cA
    eqeq1
    equsexvw
    @5
    @7
    vx
    @6
    wps
    vx
    wph
    vx
    vy
    nfs1v
    sbhypf.1
    nfbi
    @3
    @6
    wph
    @4
    wps
    @3
    wph
    @6
    wph
    vx
    vy
    sbequ12
    bicomd
    sbhypf.2
    sylan9bb
    exlimi
    sylbir
end
