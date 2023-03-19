include "cab.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "abid2.mm"
include "sseq1i.mm"
include "ss2ab.mm"
include "bitr3i.mm"

theorem ssab
  let wph: wff ph
  let vx: setvar x
  let cA: class A

  disjoint A x
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
    abid2
    sseq1i
    @1
    wph
    vx
    ss2ab
    bitr3i
end
