include "cab.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "abid2f.mm"
include "sseq2i.mm"
include "ss2ab.mm"
include "bitr3i.mm"

theorem abssf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assume abssf.1: |- F/_ x A


  assert |- ( { x | ph } C_ A <-> A. x ( ph -> x e. A ) )

  proof
    wph
    vx
    cab
    #
    cA
    wss
    @0
    vx
    cv
    cA
    wcel
    #
    vx
    cab
    #
    wss
    wph
    @1
    wi
    vx
    wal
    @2
    cA
    @0
    vx
    cA
    abssf.1
    abid2f
    sseq2i
    wph
    @1
    vx
    ss2ab
    bitr3i
end
