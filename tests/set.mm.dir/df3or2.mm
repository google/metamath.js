include "w3o.mm"
include "wo.mm"
include "wn.mm"
include "wi.mm"
include "df-3or.mm"
include "df-or.mm"
include "wa.mm"
include "ioran.mm"
include "imbi1i.mm"
include "impexp.mm"
include "bitri.mm"

theorem df3or2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph \/ ps \/ ch ) <-> ( -. ph -> ( -. ps -> ch ) ) )

  proof
    wph
    wps
    wch
    w3o
    wph
    wps
    wo
    #
    wch
    wo
    #
    wph
    wn
    #
    wps
    wn
    #
    wch
    wi
    wi
    #
    wph
    wps
    wch
    df-3or
    @1
    @0
    wn
    #
    wch
    wi
    #
    @4
    @0
    wch
    df-or
    @6
    @2
    @3
    wa
    #
    wch
    wi
    @4
    @5
    @7
    wch
    wph
    wps
    ioran
    imbi1i
    @2
    @3
    wch
    impexp
    bitri
    bitri
    bitri
end
