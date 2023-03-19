include "cv.mm"
include "co.mm"
include "cop.mm"
include "cfv.mm"
include "df-ov.mm"
include "wfun.mm"
include "wcel.mm"
include "wceq.mm"
include "coprab.mm"
include "funoprab.mm"
include "funeqi.mm"
include "mpbir.mm"
include "oprabid.mm"
include "biimpri.mm"
include "syl6eleqr.mm"
include "funopfv.mm"
include "mpsyl.mm"
include "syl5eq.mm"

theorem ovidig
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  assume ovidig.1: |- E* z ph
  assume ovidig.2: |- F = { <. <. x , y >. , z >. | ph }

  disjoint x y
  disjoint x z
  disjoint y z
  assert |- ( ph -> ( x F y ) = z )

  proof
    wph
    vx
    cv
    #
    vy
    cv
    #
    cF
    co
    @0
    @1
    cop
    #
    cF
    cfv
    #
    vz
    cv
    #
    @0
    @1
    cF
    df-ov
    cF
    wfun
    #
    wph
    @2
    @4
    cop
    #
    cF
    wcel
    @3
    @4
    wceq
    @5
    wph
    vx
    vy
    vz
    coprab
    #
    wfun
    wph
    vx
    vy
    vz
    ovidig.1
    funoprab
    cF
    @7
    ovidig.2
    funeqi
    mpbir
    wph
    @6
    @7
    cF
    @6
    @7
    wcel
    wph
    wph
    vx
    vy
    vz
    oprabid
    biimpri
    ovidig.2
    syl6eleqr
    @2
    @4
    cF
    funopfv
    mpsyl
    syl5eq
end
