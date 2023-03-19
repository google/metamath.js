include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wmo.mm"
include "wral.mm"
include "wal.mm"
include "wrex.mm"
include "wreu.mm"
include "wi.mm"
include "df-ral.mm"
include "moanimv.mm"
include "albii.mm"
include "bitr4i.mm"
include "wex.mm"
include "weu.mm"
include "2euswap.mm"
include "df-reu.mm"
include "r19.42v.mm"
include "df-rex.mm"
include "bitr3i.mm"
include "an12.mm"
include "exbii.mm"
include "bitri.mm"
include "eubii.mm"
include "3imtr4g.mm"
include "sylbi.mm"

theorem 2reuswap2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  assert |- ( A. x e. A E* y ( y e. B /\ ph ) -> ( E! x e. A E. y e. B ph -> E! y e. B E. x e. A ph ) )

  proof
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
    wa
    #
    vy
    wmo
    #
    vx
    wal
    #
    wph
    vy
    cB
    wrex
    #
    vx
    cA
    wreu
    #
    wph
    vx
    cA
    wrex
    #
    vy
    cB
    wreu
    #
    wi
    @3
    @4
    @2
    wi
    #
    vx
    wal
    @7
    @2
    vx
    cA
    df-ral
    @6
    @12
    vx
    @4
    @1
    vy
    moanimv
    albii
    bitr4i
    @7
    @5
    vy
    wex
    #
    vx
    weu
    #
    @5
    vx
    wex
    #
    vy
    weu
    #
    @9
    @11
    @5
    vx
    vy
    2euswap
    @9
    @4
    @8
    wa
    #
    vx
    weu
    @14
    @8
    vx
    cA
    df-reu
    @17
    @13
    vx
    @17
    @0
    @4
    wph
    wa
    #
    wa
    #
    vy
    wex
    #
    @13
    @17
    @18
    vy
    cB
    wrex
    @20
    @4
    wph
    vy
    cB
    r19.42v
    @18
    vy
    cB
    df-rex
    bitr3i
    @19
    @5
    vy
    @0
    @4
    wph
    an12
    exbii
    bitri
    eubii
    bitri
    @11
    @0
    @10
    wa
    #
    vy
    weu
    @16
    @10
    vy
    cB
    df-reu
    @21
    @15
    vy
    @21
    @1
    vx
    cA
    wrex
    @15
    @0
    wph
    vx
    cA
    r19.42v
    @1
    vx
    cA
    df-rex
    bitr3i
    eubii
    bitri
    3imtr4g
    sylbi
end
