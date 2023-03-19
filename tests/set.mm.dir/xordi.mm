include "wb.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "annim.mm"
include "pm5.32.mm"
include "xchbinx.mm"

theorem xordi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ -. ( ps <-> ch ) ) <-> -. ( ( ph /\ ps ) <-> ( ph /\ ch ) ) )

  proof
    wph
    wps
    wch
    wb
    #
    wn
    wa
    wph
    @0
    wi
    wph
    wps
    wa
    wph
    wch
    wa
    wb
    wph
    @0
    annim
    wph
    wps
    wch
    pm5.32
    xchbinx
end
