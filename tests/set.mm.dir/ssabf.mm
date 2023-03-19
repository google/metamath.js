include "cab.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "abid2f.mm"
include "sseq1i.mm"
include "ss2ab.mm"
include "bitr3i.mm"

theorem ssabf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assume ssabf.1: |- F/_ x A


  assert |- ( A C_ { x | ph } <-> A. x ( x e. A -> ph ) )

  proof
    cA
    wph
    vx
    cab
    #
    wss
    vx
    cv
    cA
    wcel
    #
    vx
    cab
    #
    @0
    wss
    @1
    wph
    wi
    vx
    wal
    @2
    cA
    @0
    vx
    cA
    ssabf.1
    abid2f
    sseq1i
    @1
    wph
    vx
    ss2ab
    bitr3i
end
