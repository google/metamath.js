include "cv.mm"
include "climc.mm"
include "co.mm"
include "wcel.mm"
include "cio.mm"
include "eleq1.mm"
include "cbviotav.mm"
include "wceq.mm"
include "cvv.mm"
include "weu.mm"
include "wb.mm"
include "iotaex.mm"
include "wex.mm"
include "wmo.mm"
include "c0.mm"
include "wne.mm"
include "n0.mm"
include "sylib.mm"
include "limcmo.mm"
include "eu5.mm"
include "sylanbrc.mm"
include "iota2.mm"
include "sylancr.mm"
include "mpbiri.mm"
include "syl5eqel.mm"

theorem ellimciota
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cK: class K
  let vy: setvar y
  assume ellimciota.f: |- ( ph -> F : A --> CC )
  assume ellimciota.a: |- ( ph -> A C_ CC )
  assume ellimciota.b: |- ( ph -> B e. ( ( limPt ` K ) ` A ) )
  assume ellimciota.4: |- ( ph -> ( F limCC B ) =/= (/) )
  assume ellimciota.k: |- K = ( TopOpen ` CCfld )

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint K x
  disjoint ph x
  disjoint B y
  disjoint x y
  disjoint F y
  assert |- ( ph -> ( iota x x e. ( F limCC B ) ) e. ( F limCC B ) )

  proof
    wph
    vx
    cv
    #
    cF
    cB
    climc
    co
    #
    wcel
    #
    vx
    cio
    #
    vy
    cv
    #
    @1
    wcel
    #
    vy
    cio
    #
    @1
    @2
    @5
    vx
    vy
    @0
    @4
    @1
    eleq1
    cbviotav
    #
    wph
    @6
    @1
    wcel
    #
    @3
    @6
    wceq
    #
    @7
    wph
    @6
    cvv
    wcel
    @2
    vx
    weu
    #
    @8
    @9
    wb
    @5
    vy
    iotaex
    wph
    @2
    vx
    wex
    #
    @2
    vx
    wmo
    @10
    wph
    @1
    c0
    wne
    @11
    ellimciota.4
    vx
    @1
    n0
    sylib
    wph
    vx
    cA
    cB
    cF
    cK
    ellimciota.f
    ellimciota.a
    ellimciota.b
    ellimciota.k
    limcmo
    @2
    vx
    eu5
    sylanbrc
    @2
    @8
    vx
    @6
    cvv
    @0
    @6
    @1
    eleq1
    iota2
    sylancr
    mpbiri
    syl5eqel
end
