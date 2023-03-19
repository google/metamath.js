include "nfv.mm"
include "nfvd.mm"
include "weq.mm"
include "wb.mm"
include "ex.mm"
include "bj-cbvaldv.mm"

theorem bj-cbvaldvav
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume bj-cbvaldvav.1: |- ( ( ph /\ x = y ) -> ( ps <-> ch ) )

  disjoint ps y
  disjoint ch x
  disjoint ph x
  disjoint ph y
  disjoint x y
  assert |- ( ph -> ( A. x ps <-> A. y ch ) )

  proof
    wph
    wps
    wch
    vx
    vy
    wph
    vy
    nfv
    wph
    wps
    vy
    nfvd
    wph
    vx
    vy
    weq
    wps
    wch
    wb
    bj-cbvaldvav.1
    ex
    bj-cbvaldv
end
