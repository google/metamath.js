include "wa.mm"
include "wn.mm"
include "ibar.mm"
include "bicomd.mm"
include "notbid.mm"
include "pm5.32i.mm"

theorem annotanannot
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph /\ -. ( ph /\ ps ) ) <-> ( ph /\ -. ps ) )

  proof
    wph
    wph
    wps
    wa
    #
    wn
    wps
    wn
    wph
    @0
    wps
    wph
    wps
    @0
    wph
    wps
    ibar
    bicomd
    notbid
    pm5.32i
end
