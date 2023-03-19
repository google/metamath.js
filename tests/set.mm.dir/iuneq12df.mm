include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "wb.mm"
include "wal.mm"
include "ciun.mm"
include "wceq.mm"
include "eleq2d.mm"
include "rexeqbid.mm"
include "alrimiv.mm"
include "cab.mm"
include "abbi.mm"
include "df-iun.mm"
include "eqeq12i.mm"
include "bitr4i.mm"
include "sylib.mm"

theorem iuneq12df
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vy: setvar y
  assume iuneq12df.1: |- F/ x ph
  assume iuneq12df.2: |- F/_ x A
  assume iuneq12df.3: |- F/_ x B
  assume iuneq12df.4: |- ( ph -> A = B )
  assume iuneq12df.5: |- ( ph -> C = D )


  assert |- ( ph -> U_ x e. A C = U_ x e. B D )

  proof
    wph
    vy
    cv
    #
    cC
    wcel
    #
    vx
    cA
    wrex
    #
    @0
    cD
    wcel
    #
    vx
    cB
    wrex
    #
    wb
    #
    vy
    wal
    #
    vx
    cA
    cC
    ciun
    #
    vx
    cB
    cD
    ciun
    #
    wceq
    #
    wph
    @5
    vy
    wph
    @1
    @3
    vx
    cA
    cB
    iuneq12df.1
    iuneq12df.2
    iuneq12df.3
    iuneq12df.4
    wph
    cC
    cD
    @0
    iuneq12df.5
    eleq2d
    rexeqbid
    alrimiv
    @6
    @2
    vy
    cab
    #
    @4
    vy
    cab
    #
    wceq
    @9
    @2
    @4
    vy
    abbi
    @7
    @10
    @8
    @11
    vx
    vy
    cA
    cC
    df-iun
    vx
    vy
    cB
    cD
    df-iun
    eqeq12i
    bitr4i
    sylib
end
