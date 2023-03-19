include "wreu.mm"
include "wrex.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "reu3.mm"
include "equequ1.mm"
include "equcom.mm"
include "syl6bb.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "rexbii.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "cbvrexv.mm"
include "bitri.mm"
include "anbi2i.mm"

theorem reu7
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  assume rmo4.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint ph y
  disjoint ps x
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint ph z
  disjoint ps z
  assert |- ( E! x e. A ph <-> ( E. x e. A ph /\ E. x e. A A. y e. A ( ps -> x = y ) ) )

  proof
    wph
    vx
    cA
    wreu
    wph
    vx
    cA
    wrex
    #
    wph
    vx
    vz
    weq
    #
    wi
    #
    vx
    cA
    wral
    #
    vz
    cA
    wrex
    #
    wa
    @0
    wps
    vx
    vy
    weq
    #
    wi
    #
    vy
    cA
    wral
    #
    vx
    cA
    wrex
    #
    wa
    wph
    vx
    vz
    cA
    reu3
    @4
    @8
    @0
    @4
    wps
    vz
    vy
    weq
    #
    wi
    #
    vy
    cA
    wral
    #
    vz
    cA
    wrex
    @8
    @3
    @11
    vz
    cA
    @2
    @10
    vx
    vy
    cA
    @5
    wph
    wps
    @1
    @9
    rmo4.1
    @5
    @1
    vy
    vz
    weq
    @9
    vx
    vy
    vz
    equequ1
    vy
    vz
    equcom
    syl6bb
    imbi12d
    cbvralv
    rexbii
    @11
    @7
    vz
    vx
    cA
    vz
    vx
    weq
    #
    @10
    @6
    vy
    cA
    @12
    @9
    @5
    wps
    vz
    vx
    vy
    equequ1
    imbi2d
    ralbidv
    cbvrexv
    bitri
    anbi2i
    bitri
end
