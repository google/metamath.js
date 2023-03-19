include "wcel.mm"
include "wnf.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wi.mm"
include "wal.mm"
include "wsbc.mm"
include "ex.mm"
include "alrimi.mm"
include "sbciegft.mm"
include "syl3anc.mm"

theorem sbciedf
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume sbcied.1: |- ( ph -> A e. V )
  assume sbcied.2: |- ( ( ph /\ x = A ) -> ( ps <-> ch ) )
  assume sbciedf.3: |- F/ x ph
  assume sbciedf.4: |- ( ph -> F/ x ch )

  disjoint A x
  assert |- ( ph -> ( [. A / x ]. ps <-> ch ) )

  proof
    wph
    cA
    cV
    wcel
    wch
    vx
    wnf
    vx
    cv
    cA
    wceq
    #
    wps
    wch
    wb
    #
    wi
    #
    vx
    wal
    wps
    vx
    cA
    wsbc
    wch
    wb
    sbcied.1
    sbciedf.4
    wph
    @2
    vx
    sbciedf.3
    wph
    @0
    @1
    sbcied.2
    ex
    alrimi
    wps
    wch
    vx
    cA
    cV
    sbciegft
    syl3anc
end
