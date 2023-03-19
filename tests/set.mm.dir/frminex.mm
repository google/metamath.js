include "wrex.mm"
include "crab.mm"
include "c0.mm"
include "wne.mm"
include "wfr.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "rabn0.mm"
include "cvv.mm"
include "wcel.mm"
include "wss.mm"
include "rabex.mm"
include "ssrab2.mm"
include "fri.mm"
include "ralrab.mm"
include "rexbii.mm"
include "weq.mm"
include "breq2.mm"
include "notbid.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "rexrab2.mm"
include "bitri.mm"
include "sylib.mm"
include "an4s.mm"
include "mpanl12.mm"
include "ex.mm"
include "syl5bir.mm"

theorem frminex
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vz: setvar z
  assume frminex.1: |- A e. _V
  assume frminex.2: |- ( x = y -> ( ph <-> ps ) )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint R x
  disjoint R y
  disjoint ph y
  disjoint ps x
  disjoint A z
  disjoint x z
  disjoint y z
  disjoint R z
  disjoint ph z
  disjoint ps z
  assert |- ( R Fr A -> ( E. x e. A ph -> E. x e. A ( ph /\ A. y e. A ( ps -> -. y R x ) ) ) )

  proof
    wph
    vx
    cA
    wrex
    wph
    vx
    cA
    crab
    #
    c0
    wne
    #
    cA
    cR
    wfr
    #
    wph
    wps
    vy
    cv
    #
    vx
    cv
    #
    cR
    wbr
    #
    wn
    #
    wi
    #
    vy
    cA
    wral
    #
    wa
    vx
    cA
    wrex
    #
    wph
    vx
    cA
    rabn0
    @2
    @1
    @9
    @0
    cvv
    wcel
    #
    @0
    cA
    wss
    #
    @2
    @1
    wa
    @9
    wph
    vx
    cA
    frminex.1
    rabex
    wph
    vx
    cA
    ssrab2
    @10
    @2
    @11
    @1
    @9
    @10
    @2
    wa
    @11
    @1
    wa
    wa
    @3
    vz
    cv
    #
    cR
    wbr
    #
    wn
    #
    vy
    @0
    wral
    #
    vz
    @0
    wrex
    #
    @9
    vz
    vy
    cA
    @0
    cvv
    cR
    fri
    @16
    wps
    @14
    wi
    #
    vy
    cA
    wral
    #
    vz
    @0
    wrex
    @9
    @15
    @18
    vz
    @0
    wph
    wps
    @14
    vy
    vx
    cA
    frminex.2
    ralrab
    rexbii
    wph
    @18
    @8
    vz
    vx
    cA
    vz
    vx
    weq
    #
    @17
    @7
    vy
    cA
    @19
    @14
    @6
    wps
    @19
    @13
    @5
    @12
    @4
    @3
    cR
    breq2
    notbid
    imbi2d
    ralbidv
    rexrab2
    bitri
    sylib
    an4s
    mpanl12
    ex
    syl5bir
end
