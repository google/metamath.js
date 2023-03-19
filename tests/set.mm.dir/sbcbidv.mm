include "nfv.mm"
include "sbcbid.mm"

theorem sbcbidv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume sbcbidv.1: |- ( ph -> ( ps <-> ch ) )

  disjoint ph x
  assert |- ( ph -> ( [. A / x ]. ps <-> [. A / x ]. ch ) )

  proof
    wph
    wps
    wch
    vx
    cA
    wph
    vx
    nfv
    sbcbidv.1
    sbcbid
end
