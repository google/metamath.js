include "wo.mm"
include "wn.mm"
include "wa.mm"
include "w3o.mm"
include "w3a.mm"
include "ioran.mm"
include "anbi1i.mm"
include "df-3or.mm"
include "xchnxbir.mm"
include "df-3an.mm"
include "3bitr4i.mm"

theorem 3ioran
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( -. ( ph \/ ps \/ ch ) <-> ( -. ph /\ -. ps /\ -. ch ) )

  proof
    wph
    wps
    wo
    #
    wn
    #
    wch
    wn
    #
    wa
    #
    wph
    wn
    #
    wps
    wn
    #
    wa
    #
    @2
    wa
    wph
    wps
    wch
    w3o
    #
    wn
    @4
    @5
    @2
    w3a
    @1
    @6
    @2
    wph
    wps
    ioran
    anbi1i
    @0
    wch
    wo
    @3
    @7
    @0
    wch
    ioran
    wph
    wps
    wch
    df-3or
    xchnxbir
    @4
    @5
    @2
    df-3an
    3bitr4i
end
