include "wrmo.mm"
include "wsb.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "nfv.mm"
include "rmo3f.mm"
include "sbie.mm"
include "anbi2i.mm"
include "imbi1i.mm"
include "2ralbii.mm"
include "bitri.mm"

theorem rmo4f
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume rmo4f.1: |- F/_ x A
  assume rmo4f.2: |- F/_ y A
  assume rmo4f.3: |- F/ x ps
  assume rmo4f.4: |- ( x = y -> ( ph <-> ps ) )

  disjoint x y
  disjoint ph y
  assert |- ( E* x e. A ph <-> A. x e. A A. y e. A ( ( ph /\ ps ) -> x = y ) )

  proof
    wph
    vx
    cA
    wrmo
    wph
    wph
    vx
    vy
    wsb
    #
    wa
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    cA
    wral
    vx
    cA
    wral
    wph
    wps
    wa
    #
    @2
    wi
    #
    vy
    cA
    wral
    vx
    cA
    wral
    wph
    vx
    vy
    cA
    rmo4f.1
    rmo4f.2
    wph
    vy
    nfv
    rmo3f
    @3
    @5
    vx
    vy
    cA
    cA
    @1
    @4
    @2
    @0
    wps
    wph
    wph
    wps
    vx
    vy
    rmo4f.3
    rmo4f.4
    sbie
    anbi2i
    imbi1i
    2ralbii
    bitri
end
