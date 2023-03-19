include "w-bnj17.mm"
include "w3a.mm"
include "wa.mm"
include "df-bnj17.mm"
include "hb3an.mm"
include "hban.mm"
include "hbxfrbi.mm"

theorem bnj982
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  assume bnj982.1: |- ( ph -> A. x ph )
  assume bnj982.2: |- ( ps -> A. x ps )
  assume bnj982.3: |- ( ch -> A. x ch )
  assume bnj982.4: |- ( th -> A. x th )


  assert |- ( ( ph /\ ps /\ ch /\ th ) -> A. x ( ph /\ ps /\ ch /\ th ) )

  proof
    wph
    wps
    wch
    wth
    w-bnj17
    wph
    wps
    wch
    w3a
    #
    wth
    wa
    vx
    wph
    wps
    wch
    wth
    df-bnj17
    @0
    wth
    vx
    wph
    wps
    wch
    vx
    bnj982.1
    bnj982.2
    bnj982.3
    hb3an
    bnj982.4
    hban
    hbxfrbi
end
