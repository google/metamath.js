include "w3a.mm"
include "wa.mm"
include "wn.mm"
include "w3o.mm"
include "df-3an.mm"
include "wo.mm"
include "anor.mm"
include "ianor.mm"
include "orbi1i.mm"
include "xchbinx.mm"
include "df-3or.mm"
include "xchbinxr.mm"
include "bitri.mm"

theorem 3anor
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ps /\ ch ) <-> -. ( -. ph \/ -. ps \/ -. ch ) )

  proof
    wph
    wps
    wch
    w3a
    wph
    wps
    wa
    #
    wch
    wa
    #
    wph
    wn
    #
    wps
    wn
    #
    wch
    wn
    #
    w3o
    #
    wn
    wph
    wps
    wch
    df-3an
    @1
    @2
    @3
    wo
    #
    @4
    wo
    #
    @5
    @1
    @0
    wn
    #
    @4
    wo
    @7
    @0
    wch
    anor
    @8
    @6
    @4
    wph
    wps
    ianor
    orbi1i
    xchbinx
    @2
    @3
    @4
    df-3or
    xchbinxr
    bitri
end
