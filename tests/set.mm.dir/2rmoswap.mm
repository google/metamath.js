include "wrmo.mm"
include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wmo.mm"
include "wrex.mm"
include "wi.mm"
include "df-rmo.mm"
include "ralbii.mm"
include "wal.mm"
include "df-ral.mm"
include "moanimv.mm"
include "albii.mm"
include "bitr4i.mm"
include "wex.mm"
include "2moswap.mm"
include "r19.42v.mm"
include "df-rex.mm"
include "an12.mm"
include "exbii.mm"
include "bitri.mm"
include "bitr3i.mm"
include "mobii.mm"
include "3imtr4g.mm"
include "sylbi.mm"

theorem 2rmoswap
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vk: setvar k

  disjoint A y
  disjoint x y
  disjoint B x
  disjoint k x
  assert |- ( A. x e. A E* y e. B ph -> ( E* x e. A E. y e. B ph -> E* y e. B E. x e. A ph ) )

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
    wrmo
    #
    wph
    vx
    cA
    wrex
    #
    vy
    cB
    wrmo
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
    wmo
    #
    @11
    vx
    wex
    #
    vy
    wmo
    #
    @6
    @8
    @11
    vx
    vy
    2moswap
    @6
    @10
    @5
    wa
    #
    vx
    wmo
    @16
    @5
    vx
    cA
    df-rmo
    @19
    @15
    vx
    @19
    @10
    wph
    wa
    #
    vy
    cB
    wrex
    #
    @15
    @10
    wph
    vy
    cB
    r19.42v
    @21
    @1
    @20
    wa
    #
    vy
    wex
    @15
    @20
    vy
    cB
    df-rex
    @22
    @11
    vy
    @1
    @10
    wph
    an12
    exbii
    bitri
    bitr3i
    mobii
    bitri
    @8
    @1
    @7
    wa
    #
    vy
    wmo
    @18
    @7
    vy
    cB
    df-rmo
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
    mobii
    bitri
    3imtr4g
    sylbi
    sylbi
end
