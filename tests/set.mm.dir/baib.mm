include "wa.mm"
include "ibar.mm"
include "syl6rbbr.mm"

theorem baib
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume baib.1: |- ( ph <-> ( ps /\ ch ) )


  assert |- ( ps -> ( ph <-> ch ) )

  proof
    wps
    wch
    wps
    wch
    wa
    wph
    wps
    wch
    ibar
    baib.1
    syl6rbbr
end
