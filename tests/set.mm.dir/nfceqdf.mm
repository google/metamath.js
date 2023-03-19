include "cv.mm"
include "wcel.mm"
include "wnf.mm"
include "wal.mm"
include "wnfc.mm"
include "eleq2d.mm"
include "nfbidf.mm"
include "albidv.mm"
include "df-nfc.mm"
include "3bitr4g.mm"

theorem nfceqdf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume nfceqdf.1: |- F/ x ph
  assume nfceqdf.2: |- ( ph -> A = B )


  assert |- ( ph -> ( F/_ x A <-> F/_ x B ) )

  proof
    wph
    vy
    cv
    #
    cA
    wcel
    #
    vx
    wnf
    #
    vy
    wal
    @0
    cB
    wcel
    #
    vx
    wnf
    #
    vy
    wal
    vx
    cA
    wnfc
    vx
    cB
    wnfc
    wph
    @2
    @4
    vy
    wph
    @1
    @3
    vx
    nfceqdf.1
    wph
    cA
    cB
    @0
    nfceqdf.2
    eleq2d
    nfbidf
    albidv
    vx
    vy
    cA
    df-nfc
    vx
    vy
    cB
    df-nfc
    3bitr4g
end
