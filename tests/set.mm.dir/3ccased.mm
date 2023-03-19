include "w3o.mm"
include "wa.mm"
include "wi.mm"
include "com12.mm"
include "3jaodan.mm"
include "3jaoian.mm"

theorem 3ccased
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si
  assume 3ccased.1: |- ( ph -> ( ( ch /\ et ) -> ps ) )
  assume 3ccased.2: |- ( ph -> ( ( ch /\ ze ) -> ps ) )
  assume 3ccased.3: |- ( ph -> ( ( ch /\ si ) -> ps ) )
  assume 3ccased.4: |- ( ph -> ( ( th /\ et ) -> ps ) )
  assume 3ccased.5: |- ( ph -> ( ( th /\ ze ) -> ps ) )
  assume 3ccased.6: |- ( ph -> ( ( th /\ si ) -> ps ) )
  assume 3ccased.7: |- ( ph -> ( ( ta /\ et ) -> ps ) )
  assume 3ccased.8: |- ( ph -> ( ( ta /\ ze ) -> ps ) )
  assume 3ccased.9: |- ( ph -> ( ( ta /\ si ) -> ps ) )


  assert |- ( ph -> ( ( ( ch \/ th \/ ta ) /\ ( et \/ ze \/ si ) ) -> ps ) )

  proof
    wch
    wth
    wta
    w3o
    wet
    wze
    wsi
    w3o
    #
    wa
    wph
    wps
    wch
    @0
    wph
    wps
    wi
    #
    wth
    wta
    wch
    wet
    @1
    wze
    wsi
    wph
    wch
    wet
    wa
    wps
    3ccased.1
    com12
    wph
    wch
    wze
    wa
    wps
    3ccased.2
    com12
    wph
    wch
    wsi
    wa
    wps
    3ccased.3
    com12
    3jaodan
    wth
    wet
    @1
    wze
    wsi
    wph
    wth
    wet
    wa
    wps
    3ccased.4
    com12
    wph
    wth
    wze
    wa
    wps
    3ccased.5
    com12
    wph
    wth
    wsi
    wa
    wps
    3ccased.6
    com12
    3jaodan
    wta
    wet
    @1
    wze
    wsi
    wph
    wta
    wet
    wa
    wps
    3ccased.7
    com12
    wph
    wta
    wze
    wa
    wps
    3ccased.8
    com12
    wph
    wta
    wsi
    wa
    wps
    3ccased.9
    com12
    3jaodan
    3jaoian
    com12
end
