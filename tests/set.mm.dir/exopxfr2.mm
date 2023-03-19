include "wrel.mm"
include "wrex.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "cxp.mm"
include "cop.mm"
include "wex.mm"
include "wss.mm"
include "df-rel.mm"
include "biimpi.mm"
include "sseld.mm"
include "adantrd.mm"
include "pm4.71rd.mm"
include "rexbidv2.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "exopxfr.mm"
include "syl6bb.mm"

theorem exopxfr2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  assume exopxfr2.1: |- ( x = <. y , z >. -> ( ph <-> ps ) )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint ph y
  disjoint ph z
  disjoint ps x
  assert |- ( Rel A -> ( E. x e. A ph <-> E. y E. z ( <. y , z >. e. A /\ ps ) ) )

  proof
    cA
    wrel
    #
    wph
    vx
    cA
    wrex
    vx
    cv
    #
    cA
    wcel
    #
    wph
    wa
    #
    vx
    cvv
    cvv
    cxp
    #
    wrex
    vy
    cv
    vz
    cv
    cop
    #
    cA
    wcel
    #
    wps
    wa
    #
    vz
    wex
    vy
    wex
    @0
    wph
    @3
    vx
    cA
    @4
    @0
    @3
    @1
    @4
    wcel
    #
    @0
    @2
    @8
    wph
    @0
    cA
    @4
    @1
    @0
    cA
    @4
    wss
    cA
    df-rel
    biimpi
    sseld
    adantrd
    pm4.71rd
    rexbidv2
    @3
    @7
    vx
    vy
    vz
    @1
    @5
    wceq
    @2
    @6
    wph
    wps
    @1
    @5
    cA
    eleq1
    exopxfr2.1
    anbi12d
    exopxfr
    syl6bb
end
