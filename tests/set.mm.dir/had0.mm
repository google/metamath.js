include "wn.mm"
include "whad.mm"
include "wxo.mm"
include "wb.mm"
include "had1.mm"
include "hadnot.mm"
include "xnor.mm"
include "notbi.mm"
include "bitr3i.mm"
include "3bitr4g.mm"
include "con4bid.mm"

theorem had0
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( -. ph -> ( hadd ( ph , ps , ch ) <-> ( ps \/_ ch ) ) )

  proof
    wph
    wn
    #
    wph
    wps
    wch
    whad
    #
    wps
    wch
    wxo
    #
    @0
    @0
    wps
    wn
    #
    wch
    wn
    #
    whad
    @3
    @4
    wb
    #
    @1
    wn
    @2
    wn
    #
    @0
    @3
    @4
    had1
    wph
    wps
    wch
    hadnot
    @6
    wps
    wch
    wb
    @5
    wps
    wch
    xnor
    wps
    wch
    notbi
    bitr3i
    3bitr4g
    con4bid
end
