include "wn.mm"
include "wa.mm"
include "wo.mm"
include "ioran.mm"
include "w3o.mm"
include "df-3or.mm"
include "mpbi.mm"
include "ori.mm"
include "sylbir.mm"

theorem 3ori
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume 3ori.1: |- ( ph \/ ps \/ ch )


  assert |- ( ( -. ph /\ -. ps ) -> ch )

  proof
    wph
    wn
    wps
    wn
    wa
    wph
    wps
    wo
    #
    wn
    wch
    wph
    wps
    ioran
    @0
    wch
    wph
    wps
    wch
    w3o
    @0
    wch
    wo
    3ori.1
    wph
    wps
    wch
    df-3or
    mpbi
    ori
    sylbir
end
