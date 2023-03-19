include "w3o.mm"
include "wo.mm"
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "df-3or.mm"
include "df-or.mm"
include "ioran.mm"
include "imbi1i.mm"
include "3bitri.mm"

theorem 3orit
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph \/ ps \/ ch ) <-> ( ( -. ph /\ -. ps ) -> ch ) )

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
    @0
    wn
    #
    wch
    wi
    wph
    wn
    wps
    wn
    wa
    #
    wch
    wi
    wph
    wps
    wch
    df-3or
    @0
    wch
    df-or
    @1
    @2
    wch
    wph
    wps
    ioran
    imbi1i
    3bitri
end
