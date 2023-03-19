include "wcel.mm"
include "w3a.mm"
include "cop.mm"
include "coprab.mm"
include "co.mm"
include "wceq.mm"
include "eloprabga.mm"
include "cfv.mm"
include "df-ov.mm"
include "fveq1i.mm"
include "eqtri.mm"
include "wfun.mm"
include "wi.mm"
include "funoprab.mm"
include "funopfv.mm"
include "ax-mp.mm"
include "syl5eq.mm"
include "syl6bir.mm"

theorem ovigg
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  assume ovigg.1: |- ( ( x = A /\ y = B /\ z = C ) -> ( ph <-> ps ) )
  assume ovigg.4: |- E* z ph
  assume ovigg.5: |- F = { <. <. x , y >. , z >. | ph }

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint ps x
  disjoint ps y
  disjoint ps z
  assert |- ( ( A e. V /\ B e. W /\ C e. X ) -> ( ps -> ( A F B ) = C ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    cC
    cX
    wcel
    w3a
    wps
    cA
    cB
    cop
    #
    cC
    cop
    wph
    vx
    vy
    vz
    coprab
    #
    wcel
    #
    cA
    cB
    cF
    co
    #
    cC
    wceq
    wph
    wps
    vx
    vy
    vz
    cA
    cB
    cC
    cV
    cW
    cX
    ovigg.1
    eloprabga
    @2
    @3
    @0
    @1
    cfv
    #
    cC
    @3
    @0
    cF
    cfv
    @4
    cA
    cB
    cF
    df-ov
    @0
    cF
    @1
    ovigg.5
    fveq1i
    eqtri
    @1
    wfun
    @2
    @4
    cC
    wceq
    wi
    wph
    vx
    vy
    vz
    ovigg.4
    funoprab
    @0
    cC
    @1
    funopfv
    ax-mp
    syl5eq
    syl6bir
end
