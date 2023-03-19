include "wo.mm"
include "wsbc.mm"
include "sbcor.mm"
include "orbi12i.mm"
include "bitri.mm"

theorem sbcori
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wet: wff et
  let vx: setvar x
  let cA: class A
  assume sbcori.1: |- ( [. A / x ]. ph <-> ch )
  assume sbcori.2: |- ( [. A / x ]. ps <-> et )


  assert |- ( [. A / x ]. ( ph \/ ps ) <-> ( ch \/ et ) )

  proof
    wph
    wps
    wo
    vx
    cA
    wsbc
    wph
    vx
    cA
    wsbc
    #
    wps
    vx
    cA
    wsbc
    #
    wo
    wch
    wet
    wo
    wph
    wps
    vx
    cA
    sbcor
    @0
    wch
    @1
    wet
    sbcori.1
    sbcori.2
    orbi12i
    bitri
end
