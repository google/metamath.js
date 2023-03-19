include "wa.mm"
include "anbi2i.mm"
include "anass.mm"
include "bitr4i.mm"

theorem bianass
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wet: wff et
  assume bianass.1: |- ( ph <-> ( ps /\ ch ) )


  assert |- ( ( et /\ ph ) <-> ( ( et /\ ps ) /\ ch ) )

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
    wet
    wps
    wa
    wch
    wa
    wph
    @0
    wet
    bianass.1
    anbi2i
    wet
    wps
    wch
    anass
    bitr4i
end
