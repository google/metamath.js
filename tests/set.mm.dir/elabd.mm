include "cvv.mm"
include "wcel.mm"
include "wex.mm"
include "spcegv.mm"
include "sylc.mm"

theorem elabd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cX: class X
  assume elab.xex: |- ( ph -> X e. _V )
  assume elab.xmaj: |- ( ph -> ch )
  assume elab.xsub: |- ( x = X -> ( ps <-> ch ) )

  disjoint ch x
  disjoint X x
  assert |- ( ph -> E. x ps )

  proof
    wph
    cX
    cvv
    wcel
    wch
    wps
    vx
    wex
    elab.xex
    elab.xmaj
    wps
    wch
    vx
    cX
    cvv
    elab.xsub
    spcegv
    sylc
end
