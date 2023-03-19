include "wreu.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "weu.mm"
include "w3a.mm"
include "df-reu.mm"
include "reubii.mm"
include "euanv.mm"
include "bicomi.mm"
include "3anass.mm"
include "eubii.mm"
include "bitri.mm"

theorem 2reu5lem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint A y
  disjoint B x
  disjoint x y
  assert |- ( E! x e. A E! y e. B ph <-> E! x E! y ( x e. A /\ y e. B /\ ph ) )

  proof
    wph
    vy
    cB
    wreu
    #
    vx
    cA
    wreu
    vy
    cv
    cB
    wcel
    #
    wph
    wa
    #
    vy
    weu
    #
    vx
    cA
    wreu
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
    weu
    #
    vx
    weu
    #
    @0
    @3
    vx
    cA
    wph
    vy
    cB
    df-reu
    reubii
    @4
    @5
    @3
    wa
    #
    vx
    weu
    @8
    @3
    vx
    cA
    df-reu
    @9
    @7
    vx
    @9
    @5
    @2
    wa
    #
    vy
    weu
    #
    @7
    @11
    @9
    @5
    @2
    vy
    euanv
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
    eubii
    bitri
    eubii
    bitri
    bitri
end
