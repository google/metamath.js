include "nfv.mm"
include "wnf.mm"
include "a1i.mm"
include "bj-cbv2v.mm"

theorem bj-cbvaldv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume bj-cbvaldv.1: |- F/ y ph
  assume bj-cbvaldv.2: |- ( ph -> F/ y ps )
  assume bj-cbvaldv.3: |- ( ph -> ( x = y -> ( ps <-> ch ) ) )

  disjoint x y
  disjoint ph x
  disjoint ch x
  assert |- ( ph -> ( A. x ps <-> A. y ch ) )

  proof
    wph
    wps
    wch
    vx
    vy
    wph
    vx
    nfv
    bj-cbvaldv.1
    bj-cbvaldv.2
    wch
    vx
    wnf
    wph
    wch
    vx
    nfv
    a1i
    bj-cbvaldv.3
    bj-cbv2v
end
