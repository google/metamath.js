include "wsbc.mm"
include "cvv.mm"
include "wcel.mm"
include "a1i.mm"
include "spsbcd.mm"
include "sylib.mm"

theorem spsbcdi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume spsbcdi.1: |- A e. _V
  assume spsbcdi.2: |- ( ph -> A. x ch )
  assume spsbcdi.3: |- ( [. A / x ]. ch <-> ps )


  assert |- ( ph -> ps )

  proof
    wph
    wch
    vx
    cA
    wsbc
    wps
    wph
    wch
    vx
    cA
    cvv
    cA
    cvv
    wcel
    wph
    spsbcdi.1
    a1i
    spsbcdi.2
    spsbcd
    spsbcdi.3
    sylib
end
