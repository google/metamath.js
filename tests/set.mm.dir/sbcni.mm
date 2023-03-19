include "wn.mm"
include "wsbc.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "sbcng.mm"
include "ax-mp.mm"
include "xchbinx.mm"

theorem sbcni
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume sbcni.1: |- A e. _V
  assume sbcni.2: |- ( [. A / x ]. ph <-> ps )


  assert |- ( [. A / x ]. -. ph <-> -. ps )

  proof
    wph
    wn
    vx
    cA
    wsbc
    #
    wph
    vx
    cA
    wsbc
    #
    wps
    cA
    cvv
    wcel
    @0
    @1
    wn
    wb
    sbcni.1
    wph
    vx
    cA
    cvv
    sbcng
    ax-mp
    sbcni.2
    xchbinx
end
