include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "weq.mm"
include "wn.mm"
include "eleq1.mm"
include "dvelimv.mm"
include "ex.mm"
include "alimi.mm"
include "syl6com.mm"
include "biimpd.mm"
include "syli.mm"
include "pm2.61d2.mm"
include "df-ral.mm"
include "sylibr.mm"
include "rgen.mm"

theorem rgen2a
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  assume rgen2a.1: |- ( ( x e. A /\ y e. A ) -> ph )

  disjoint A y
  disjoint y z
  disjoint A z
  disjoint x z
  assert |- A. x e. A A. y e. A ph

  proof
    wph
    vy
    cA
    wral
    #
    vx
    cA
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cA
    wcel
    #
    wph
    wi
    #
    vy
    wal
    #
    @0
    @2
    vy
    vx
    weq
    #
    vy
    wal
    #
    @6
    @8
    wn
    @2
    @2
    vy
    wal
    @6
    vz
    cv
    #
    cA
    wcel
    @2
    vy
    vx
    vz
    @9
    @1
    cA
    eleq1
    dvelimv
    @2
    @5
    vy
    @2
    @4
    wph
    rgen2a.1
    ex
    #
    alimi
    syl6com
    @7
    @5
    vy
    @4
    @7
    @2
    wph
    @7
    @4
    @2
    @3
    @1
    cA
    eleq1
    biimpd
    @10
    syli
    alimi
    pm2.61d2
    wph
    vy
    cA
    df-ral
    sylibr
    rgen
end
