include "wrmo.mm"
include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wmo.mm"
include "w3a.mm"
include "wal.mm"
include "df-rmo.mm"
include "ralbii.mm"
include "wi.mm"
include "df-ral.mm"
include "moanimv.mm"
include "bicomi.mm"
include "3anass.mm"
include "mobii.mm"
include "bitri.mm"
include "albii.mm"

theorem 2reu5lem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint A y
  disjoint B x
  disjoint x y
  assert |- ( A. x e. A E* y e. B ph <-> A. x E* y ( x e. A /\ y e. B /\ ph ) )

  proof
    wph
    vy
    cB
    wrmo
    #
    vx
    cA
    wral
    vy
    cv
    cB
    wcel
    #
    wph
    wa
    #
    vy
    wmo
    #
    vx
    cA
    wral
    #
    vx
    cv
    cA
    wcel
    #
    @1
    wph
    w3a
    #
    vy
    wmo
    #
    vx
    wal
    #
    @0
    @3
    vx
    cA
    wph
    vy
    cB
    df-rmo
    ralbii
    @4
    @5
    @3
    wi
    #
    vx
    wal
    @8
    @3
    vx
    cA
    df-ral
    @9
    @7
    vx
    @9
    @5
    @2
    wa
    #
    vy
    wmo
    #
    @7
    @11
    @9
    @5
    @2
    vy
    moanimv
    bicomi
    @10
    @6
    vy
    @6
    @10
    @5
    @1
    wph
    3anass
    bicomi
    mobii
    bitri
    albii
    bitri
    bitri
end
