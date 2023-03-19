include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "w3a.mm"
include "r2al.mm"
include "19.21v.mm"
include "df-3an.mm"
include "imbi1i.mm"
include "impexp.mm"
include "bitri.mm"
include "albii.mm"
include "df-ral.mm"
include "imbi2i.mm"
include "3bitr4ri.mm"
include "2albii.mm"

theorem r3al
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B z
  assert |- ( A. x e. A A. y e. B A. z e. C ph <-> A. x A. y A. z ( ( x e. A /\ y e. B /\ z e. C ) -> ph ) )

  proof
    wph
    vz
    cC
    wral
    #
    vy
    cB
    wral
    vx
    cA
    wral
    vx
    cv
    cA
    wcel
    #
    vy
    cv
    cB
    wcel
    #
    wa
    #
    @0
    wi
    #
    vy
    wal
    vx
    wal
    @1
    @2
    vz
    cv
    cC
    wcel
    #
    w3a
    #
    wph
    wi
    #
    vz
    wal
    #
    vy
    wal
    vx
    wal
    @0
    vx
    vy
    cA
    cB
    r2al
    @4
    @8
    vx
    vy
    @3
    @5
    wph
    wi
    #
    wi
    #
    vz
    wal
    @3
    @9
    vz
    wal
    #
    wi
    @8
    @4
    @3
    @9
    vz
    19.21v
    @7
    @10
    vz
    @7
    @3
    @5
    wa
    #
    wph
    wi
    @10
    @6
    @12
    wph
    @1
    @2
    @5
    df-3an
    imbi1i
    @3
    @5
    wph
    impexp
    bitri
    albii
    @0
    @11
    @3
    wph
    vz
    cC
    df-ral
    imbi2i
    3bitr4ri
    2albii
    bitri
end
