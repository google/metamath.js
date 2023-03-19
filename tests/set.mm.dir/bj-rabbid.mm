include "wb.mm"
include "cv.mm"
include "wcel.mm"
include "adantr.mm"
include "bj-rabbida.mm"

theorem bj-rabbid
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume bj-rabbid.nf: |- F/ x ph
  assume bj-rabbid.1: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> { x e. A | ps } = { x e. A | ch } )

  proof
    wph
    wps
    wch
    vx
    cA
    bj-rabbid.nf
    wph
    wps
    wch
    wb
    vx
    cv
    cA
    wcel
    bj-rabbid.1
    adantr
    bj-rabbida
end
