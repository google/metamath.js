include "wrex.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "weq.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "biimpd.mm"
include "syli.mm"
include "impancom.mm"
include "rexlimiva.mm"
include "imp.mm"

theorem rexraleqim
  let wph: wff ph
  let wps: wff ps
  let wth: wff th
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cY: class Y
  assume rexraleqim.1: |- ( x = z -> ( ps <-> ph ) )
  assume rexraleqim.2: |- ( z = Y -> ( ph <-> th ) )

  disjoint A x
  disjoint A z
  disjoint x z
  disjoint Y x
  disjoint Y z
  disjoint ph x
  disjoint ps z
  disjoint th z
  assert |- ( ( E. z e. A ph /\ A. x e. A ( ps -> x = Y ) ) -> th )

  proof
    wph
    vz
    cA
    wrex
    wps
    vx
    cv
    #
    cY
    wceq
    #
    wi
    #
    vx
    cA
    wral
    #
    wth
    wph
    @3
    wth
    wi
    vz
    cA
    vz
    cv
    #
    cA
    wcel
    #
    @3
    wph
    wth
    wph
    @5
    @3
    wa
    @4
    cY
    wceq
    #
    wth
    @2
    wph
    @6
    wi
    vx
    @4
    cA
    vx
    vz
    weq
    wps
    wph
    @1
    @6
    rexraleqim.1
    @0
    @4
    cY
    eqeq1
    imbi12d
    rspcva
    @6
    wph
    wth
    rexraleqim.2
    biimpd
    syli
    impancom
    rexlimiva
    imp
end
