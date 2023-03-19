include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "wcel.mm"
include "wb.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elabg.mm"
include "syl.mm"
include "biimpa.mm"
include "wa.mm"
include "simpr.mm"
include "adantr.mm"
include "biimpar.mm"
include "syl2anc.mm"
include "exp31.mm"
include "rexlimd.mm"
include "imp.mm"
include "syldan.mm"

theorem elabreximd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  assume elabreximd.1: |- F/ x ph
  assume elabreximd.2: |- F/ x ch
  assume elabreximd.3: |- ( A = B -> ( ch <-> ps ) )
  assume elabreximd.4: |- ( ph -> A e. V )
  assume elabreximd.5: |- ( ( ph /\ x e. C ) -> ps )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint C y
  assert |- ( ( ph /\ A e. { y | E. x e. C y = B } ) -> ch )

  proof
    wph
    cA
    vy
    cv
    #
    cB
    wceq
    #
    vx
    cC
    wrex
    #
    vy
    cab
    wcel
    #
    cA
    cB
    wceq
    #
    vx
    cC
    wrex
    #
    wch
    wph
    @3
    @5
    wph
    cA
    cV
    wcel
    @3
    @5
    wb
    elabreximd.4
    @2
    @5
    vy
    cA
    cV
    @0
    cA
    wceq
    @1
    @4
    vx
    cC
    @0
    cA
    cB
    eqeq1
    rexbidv
    elabg
    syl
    biimpa
    wph
    @5
    wch
    wph
    @4
    wch
    vx
    cC
    elabreximd.1
    elabreximd.2
    wph
    vx
    cv
    cC
    wcel
    #
    @4
    wch
    wph
    @6
    wa
    #
    @4
    wa
    @4
    wps
    wch
    @7
    @4
    simpr
    @7
    wps
    @4
    elabreximd.5
    adantr
    @4
    wch
    wps
    elabreximd.3
    biimpar
    syl2anc
    exp31
    rexlimd
    imp
    syldan
end
