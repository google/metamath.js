include "wi.mm"
include "wn.mm"
include "wa.mm"
include "confun.mm"

theorem confun2
  let wph: wff ph
  let wps: wff ps
  let vk: setvar k
  let vx: setvar x
  assume confun2.1: |- ( ps -> ph )
  assume confun2.2: |- ( ps -> -. ( ps -> ( ps /\ -. ps ) ) )
  assume confun2.3: |- ( ( ps -> ph ) -> ( ( ps -> ph ) -> ph ) )


  assert |- ( ps -> ( -. ( ps -> ( ps /\ -. ps ) ) <-> ( ps -> ph ) ) )

  proof
    wps
    wph
    wi
    wph
    wps
    wps
    wps
    wps
    wn
    wa
    wi
    wn
    confun2.1
    confun2.1
    confun2.2
    confun2.3
    confun
end
