include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "wb.mm"
include "wal.mm"
include "ciun.mm"
include "wceq.mm"
include "wa.mm"
include "eleq2d.mm"
include "rexbida.mm"
include "rexeqf.mm"
include "syl.mm"
include "bitrd.mm"
include "alrimiv.mm"
include "cab.mm"
include "abbi.mm"
include "df-iun.mm"
include "eqeq12i.mm"
include "bitr4i.mm"
include "sylib.mm"

theorem iuneq12daf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vy: setvar y
  assume iuneq12daf.1: |- F/ x ph
  assume iuneq12daf.2: |- F/_ x A
  assume iuneq12daf.3: |- F/_ x B
  assume iuneq12daf.4: |- ( ph -> A = B )
  assume iuneq12daf.5: |- ( ( ph /\ x e. A ) -> C = D )


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
    @2
    @3
    vx
    cA
    wrex
    #
    @4
    wph
    @1
    @3
    vx
    cA
    iuneq12daf.1
    wph
    vx
    cv
    cA
    wcel
    wa
    cC
    cD
    @0
    iuneq12daf.5
    eleq2d
    rexbida
    wph
    cA
    cB
    wceq
    @10
    @4
    wb
    iuneq12daf.4
    @3
    vx
    cA
    cB
    iuneq12daf.2
    iuneq12daf.3
    rexeqf
    syl
    bitrd
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
    @11
    @8
    @12
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
