include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "cab.mm"
include "wss.mm"
include "alrimiv.mm"
include "abss.mm"
include "sylibr.mm"

theorem abssdv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume abssdv.1: |- ( ph -> ( ps -> x e. A ) )

  disjoint ph x
  disjoint A x
  assert |- ( ph -> { x | ps } C_ A )

  proof
    wph
    wps
    vx
    cv
    cA
    wcel
    wi
    #
    vx
    wal
    wps
    vx
    cab
    cA
    wss
    wph
    @0
    vx
    abssdv.1
    alrimiv
    wps
    vx
    cA
    abss
    sylibr
end
