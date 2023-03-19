include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "wcel.mm"
include "biimpd.mm"
include "ax-gen.mm"
include "nfv.mm"
include "nfcv.mm"
include "spcimgft.mm"
include "mpsyl.mm"

theorem spcdvw
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  assume spcdvw.1: |- ( ph -> A e. B )
  assume spcdvw.2: |- ( x = A -> ( ps <-> ch ) )

  disjoint A x
  disjoint ch x
  disjoint k x
  assert |- ( ph -> ( A. x ps -> ch ) )

  proof
    vx
    cv
    cA
    wceq
    #
    wps
    wch
    wi
    wi
    #
    vx
    wal
    wph
    cA
    cB
    wcel
    wps
    vx
    wal
    wch
    wi
    @1
    vx
    @0
    wps
    wch
    spcdvw.2
    biimpd
    ax-gen
    spcdvw.1
    wps
    wch
    vx
    cA
    cB
    wch
    vx
    nfv
    vx
    cA
    nfcv
    spcimgft
    mpsyl
end
