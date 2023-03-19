include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wex.mm"
include "wrmo.mm"
include "impexp.mm"
include "ralbii.mm"
include "r19.21.mm"
include "bitri.mm"
include "exbii.mm"
include "nfv.mm"
include "rmo2.mm"
include "imbi2i.mm"
include "19.37v.mm"
include "bitr4i.mm"
include "3bitr4i.mm"

theorem rmoanim
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vk: setvar k
  assume rmoanim.1: |- F/ x ph

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint ph y
  disjoint ps y
  disjoint k x
  assert |- ( E* x e. A ( ph /\ ps ) <-> ( ph -> E* x e. A ps ) )

  proof
    wph
    wps
    wa
    #
    vx
    vy
    weq
    #
    wi
    #
    vx
    cA
    wral
    #
    vy
    wex
    wph
    wps
    @1
    wi
    #
    vx
    cA
    wral
    #
    wi
    #
    vy
    wex
    #
    @0
    vx
    cA
    wrmo
    wph
    wps
    vx
    cA
    wrmo
    #
    wi
    #
    @3
    @6
    vy
    @3
    wph
    @4
    wi
    #
    vx
    cA
    wral
    @6
    @2
    @10
    vx
    cA
    wph
    wps
    @1
    impexp
    ralbii
    wph
    @4
    vx
    cA
    rmoanim.1
    r19.21
    bitri
    exbii
    @0
    vx
    vy
    cA
    @0
    vy
    nfv
    rmo2
    @9
    wph
    @5
    vy
    wex
    #
    wi
    @7
    @8
    @11
    wph
    wps
    vx
    vy
    cA
    wps
    vy
    nfv
    rmo2
    imbi2i
    wph
    @5
    vy
    19.37v
    bitr4i
    3bitr4i
end
