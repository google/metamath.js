include "wrex.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "rexsb.mm"
include "cv.mm"
include "wcel.mm"
include "alral.mm"
include "df-ral.mm"
include "wa.mm"
include "19.27v.mm"
include "pm2.04.mm"
include "eleq1.mm"
include "biimprd.mm"
include "pm2.83.mm"
include "ax-mp.mm"
include "3syl.mm"
include "imp.mm"
include "alimi.mm"
include "sylbir.mm"
include "ex.mm"
include "sylbi.mm"
include "com12.mm"
include "impbid2.mm"
include "rexbiia.mm"
include "bitri.mm"

theorem rexrsb
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vk: setvar k

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint ph y
  disjoint k x
  assert |- ( E. x e. A ph <-> E. y e. A A. x e. A ( x = y -> ph ) )

  proof
    wph
    vx
    cA
    wrex
    vx
    vy
    weq
    #
    wph
    wi
    #
    vx
    wal
    #
    vy
    cA
    wrex
    @1
    vx
    cA
    wral
    #
    vy
    cA
    wrex
    wph
    vx
    vy
    cA
    rexsb
    @2
    @3
    vy
    cA
    vy
    cv
    #
    cA
    wcel
    #
    @2
    @3
    @1
    vx
    cA
    alral
    @3
    @5
    @2
    @3
    vx
    cv
    #
    cA
    wcel
    #
    @1
    wi
    #
    vx
    wal
    #
    @5
    @2
    wi
    @1
    vx
    cA
    df-ral
    @9
    @5
    @2
    @9
    @5
    wa
    @8
    @5
    wa
    #
    vx
    wal
    @2
    @8
    @5
    vx
    19.27v
    @10
    @1
    vx
    @8
    @5
    @1
    @8
    @0
    @7
    wph
    wi
    wi
    #
    @0
    @5
    wph
    wi
    wi
    #
    @5
    @1
    wi
    @7
    @0
    wph
    pm2.04
    @0
    @5
    @7
    wi
    wi
    @11
    @12
    wi
    @0
    @7
    @5
    @6
    @4
    cA
    eleq1
    biimprd
    @0
    @5
    @7
    wph
    pm2.83
    ax-mp
    @0
    @5
    wph
    pm2.04
    3syl
    imp
    alimi
    sylbir
    ex
    sylbi
    com12
    impbid2
    rexbiia
    bitri
end
