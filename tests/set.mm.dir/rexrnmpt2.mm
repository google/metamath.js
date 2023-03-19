include "wcel.mm"
include "wral.mm"
include "wn.mm"
include "crn.mm"
include "wrex.mm"
include "cv.mm"
include "wceq.mm"
include "notbid.mm"
include "ralrnmpt2.mm"
include "dfrex2.mm"
include "rexbii.mm"
include "rexnal.mm"
include "bitri.mm"
include "3bitr4g.mm"

theorem rexrnmpt2
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
  let vw: setvar w
  let cD: class D
  assume rngop.1: |- F = ( x e. A , y e. B |-> C )
  assume ralrnmpt2.2: |- ( z = C -> ( ph <-> ps ) )

  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint F z
  disjoint ps z
  disjoint x y
  disjoint x z
  disjoint ph x
  disjoint ph y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint B w
  disjoint C w
  disjoint F w
  disjoint D x
  disjoint D y
  disjoint D z
  assert |- ( A. x e. A A. y e. B C e. V -> ( E. z e. ran F ph <-> E. x e. A E. y e. B ps ) )

  proof
    cC
    cV
    wcel
    vy
    cB
    wral
    vx
    cA
    wral
    #
    wph
    wn
    #
    vz
    cF
    crn
    #
    wral
    #
    wn
    wps
    wn
    #
    vy
    cB
    wral
    #
    vx
    cA
    wral
    #
    wn
    #
    wph
    vz
    @2
    wrex
    wps
    vy
    cB
    wrex
    #
    vx
    cA
    wrex
    #
    @0
    @3
    @6
    @1
    @4
    vx
    vy
    vz
    cA
    cB
    cC
    cF
    cV
    rngop.1
    vz
    cv
    cC
    wceq
    wph
    wps
    ralrnmpt2.2
    notbid
    ralrnmpt2
    notbid
    wph
    vz
    @2
    dfrex2
    @9
    @5
    wn
    #
    vx
    cA
    wrex
    @7
    @8
    @10
    vx
    cA
    wps
    vy
    cB
    dfrex2
    rexbii
    @5
    vx
    cA
    rexnal
    bitri
    3bitr4g
end
