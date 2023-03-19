include "wa.mm"
include "wsbc.mm"
include "sbcan.mm"
include "anbi12i.mm"
include "bitri.mm"

theorem sbcani
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wet: wff et
  let vx: setvar x
  let cA: class A
  assume sbcani.1: |- ( [. A / x ]. ph <-> ch )
  assume sbcani.2: |- ( [. A / x ]. ps <-> et )


  assert |- ( [. A / x ]. ( ph /\ ps ) <-> ( ch /\ et ) )

  proof
    wph
    wps
    wa
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
    wa
    wch
    wet
    wa
    wph
    wps
    vx
    cA
    sbcan
    @0
    wch
    @1
    wet
    sbcani.1
    sbcani.2
    anbi12i
    bitri
end
