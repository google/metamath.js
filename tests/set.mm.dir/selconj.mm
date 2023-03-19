include "wa.mm"
include "anbi2i.mm"
include "an12.mm"
include "bitr4i.mm"

theorem selconj
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wet: wff et
  assume selconj.1: |- ( ph <-> ( ps /\ ch ) )


  assert |- ( ( et /\ ph ) <-> ( ps /\ ( et /\ ch ) ) )

  proof
    wet
    wph
    wa
    wet
    wps
    wch
    wa
    #
    wa
    wps
    wet
    wch
    wa
    wa
    wph
    @0
    wet
    selconj.1
    anbi2i
    wps
    wet
    wch
    an12
    bitr4i
end
