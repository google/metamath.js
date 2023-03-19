include "cv.mm"
include "wcel.mm"
include "wnf.mm"
include "wal.mm"
include "wnfc.mm"
include "alrimi.mm"
include "df-nfc.mm"
include "sylibr.mm"

theorem nfcd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume nfcd.1: |- F/ y ph
  assume nfcd.2: |- ( ph -> F/ x y e. A )

  disjoint x y
  disjoint A y
  assert |- ( ph -> F/_ x A )

  proof
    wph
    vy
    cv
    cA
    wcel
    vx
    wnf
    #
    vy
    wal
    vx
    cA
    wnfc
    wph
    @0
    vy
    nfcd.1
    nfcd.2
    alrimi
    vx
    vy
    cA
    df-nfc
    sylibr
end
