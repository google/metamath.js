include "wrmo.mm"
include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wmo.mm"
include "wrex.mm"
include "wreu.mm"
include "wi.mm"
include "df-rmo.mm"
include "ralbii.mm"
include "wal.mm"
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

theorem 2reuswap
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  assert |- ( A. x e. A E* y e. B ph -> ( E! x e. A E. y e. B ph -> E! y e. B E. x e. A ph ) )

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
    vx
    cv
    cA
    wcel
    #
    @2
    wa
    #
    vy
    wmo
    #
    vx
    wal
    #
    @9
    @4
    @10
    @3
    wi
    #
    vx
    wal
    @13
    @3
    vx
    cA
    df-ral
    @12
    @14
    vx
    @10
    @2
    vy
    moanimv
    albii
    bitr4i
    @13
    @11
    vy
    wex
    #
    vx
    weu
    #
    @11
    vx
    wex
    #
    vy
    weu
    #
    @6
    @8
    @11
    vx
    vy
    2euswap
    @6
    @10
    @5
    wa
    #
    vx
    weu
    @16
    @5
    vx
    cA
    df-reu
    @19
    @15
    vx
    @19
    @1
    @10
    wph
    wa
    #
    wa
    #
    vy
    wex
    #
    @15
    @19
    @20
    vy
    cB
    wrex
    @22
    @10
    wph
    vy
    cB
    r19.42v
    @20
    vy
    cB
    df-rex
    bitr3i
    @21
    @11
    vy
    @1
    @10
    wph
    an12
    exbii
    bitri
    eubii
    bitri
    @8
    @1
    @7
    wa
    #
    vy
    weu
    @18
    @7
    vy
    cB
    df-reu
    @23
    @17
    vy
    @23
    @2
    vx
    cA
    wrex
    @17
    @1
    wph
    vx
    cA
    r19.42v
    @2
    vx
    cA
    df-rex
    bitr3i
    eubii
    bitri
    3imtr4g
    sylbi
    sylbi
end
