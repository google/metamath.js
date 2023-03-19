include "wn.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "wral.mm"
include "wrex.mm"
include "cop.mm"
include "wceq.mm"
include "notbid.mm"
include "raliunxp.mm"
include "ralnex.mm"
include "ralbii.mm"
include "bitri.mm"
include "notbii.mm"
include "dfrex2.mm"
include "3bitr4i.mm"

theorem rexiunxp
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  assume ralxp.1: |- ( x = <. y , z >. -> ( ph <-> ps ) )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B z
  disjoint ph y
  disjoint ph z
  disjoint ps x
  assert |- ( E. x e. U_ y e. A ( { y } X. B ) ph <-> E. y e. A E. z e. B ps )

  proof
    wph
    wn
    #
    vx
    vy
    cA
    vy
    cv
    #
    csn
    cB
    cxp
    ciun
    #
    wral
    #
    wn
    wps
    vz
    cB
    wrex
    #
    wn
    #
    vy
    cA
    wral
    #
    wn
    wph
    vx
    @2
    wrex
    @4
    vy
    cA
    wrex
    @3
    @6
    @3
    wps
    wn
    #
    vz
    cB
    wral
    #
    vy
    cA
    wral
    @6
    @0
    @7
    vx
    vy
    vz
    cA
    cB
    vx
    cv
    @1
    vz
    cv
    cop
    wceq
    wph
    wps
    ralxp.1
    notbid
    raliunxp
    @8
    @5
    vy
    cA
    wps
    vz
    cB
    ralnex
    ralbii
    bitri
    notbii
    wph
    vx
    @2
    dfrex2
    @4
    vy
    cA
    dfrex2
    3bitr4i
end
