include "wa.mm"
include "w3a.mm"
include "df-3an.mm"
include "mtbi.mm"
include "imnani.mm"

theorem bj-imn3ani
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume bj-imn3ani.1: |- -. ( ph /\ ps /\ ch )


  assert |- ( ( ph /\ ps ) -> -. ch )

  proof
    wph
    wps
    wa
    #
    wch
    wph
    wps
    wch
    w3a
    @0
    wch
    wa
    bj-imn3ani.1
    wph
    wps
    wch
    df-3an
    mtbi
    imnani
end
