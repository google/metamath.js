include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "wsbc.mm"
include "spsbc.mm"
include "sbcbig.mm"
include "sylibd.mm"

theorem sbcbi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> ( A. x ( ph <-> ps ) -> ( [. A / x ]. ph <-> [. A / x ]. ps ) ) )

  proof
    cA
    cV
    wcel
    wph
    wps
    wb
    #
    vx
    wal
    @0
    vx
    cA
    wsbc
    wph
    vx
    cA
    wsbc
    wps
    vx
    cA
    wsbc
    wb
    @0
    vx
    cA
    cV
    spsbc
    wph
    wps
    vx
    cA
    cV
    sbcbig
    sylibd
end
