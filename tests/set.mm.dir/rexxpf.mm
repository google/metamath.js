include "wn.mm"
include "cxp.mm"
include "wral.mm"
include "wrex.mm"
include "nfn.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "notbid.mm"
include "ralxpf.mm"
include "ralnex.mm"
include "ralbii.mm"
include "bitri.mm"
include "notbii.mm"
include "dfrex2.mm"
include "3bitr4i.mm"

theorem rexxpf
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume ralxpf.1: |- F/ y ph
  assume ralxpf.2: |- F/ z ph
  assume ralxpf.3: |- F/ x ps
  assume ralxpf.4: |- ( x = <. y , z >. -> ( ph <-> ps ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint u z
  disjoint B u
  disjoint v z
  disjoint B v
  disjoint w z
  disjoint B w
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ps u
  disjoint ps v
  disjoint ps w
  assert |- ( E. x e. ( A X. B ) ph <-> E. y e. A E. z e. B ps )

  proof
    wph
    wn
    #
    vx
    cA
    cB
    cxp
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
    @1
    wrex
    @3
    vy
    cA
    wrex
    @2
    @5
    @2
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
    @5
    @0
    @6
    vx
    vy
    vz
    cA
    cB
    wph
    vy
    ralxpf.1
    nfn
    wph
    vz
    ralxpf.2
    nfn
    wps
    vx
    ralxpf.3
    nfn
    vx
    cv
    vy
    cv
    vz
    cv
    cop
    wceq
    wph
    wps
    ralxpf.4
    notbid
    ralxpf
    @7
    @4
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
    @1
    dfrex2
    @3
    vy
    cA
    dfrex2
    3bitr4i
end
