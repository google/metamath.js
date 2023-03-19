include "wi.mm"
include "wsbc.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "sbcimg.mm"
include "ax-mp.mm"
include "imbi12i.mm"
include "bitri.mm"

theorem sbcimi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wet: wff et
  let vx: setvar x
  let cA: class A
  assume sbcimi.1: |- A e. _V
  assume sbcimi.2: |- ( [. A / x ]. ph <-> ch )
  assume sbcimi.3: |- ( [. A / x ]. ps <-> et )


  assert |- ( [. A / x ]. ( ph -> ps ) <-> ( ch -> et ) )

  proof
    wph
    wps
    wi
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
    vx
    cA
    wsbc
    #
    wi
    #
    wch
    wet
    wi
    cA
    cvv
    wcel
    @0
    @3
    wb
    sbcimi.1
    wph
    wps
    vx
    cA
    cvv
    sbcimg
    ax-mp
    @1
    wch
    @2
    wet
    sbcimi.2
    sbcimi.3
    imbi12i
    bitri
end
