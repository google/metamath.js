include "wn.mm"
include "wa.mm"
include "wb.mm"
include "ibar.mm"
include "nbbn.mm"
include "sylib.mm"
include "con2i.mm"

theorem pclem6
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph <-> ( ps /\ -. ph ) ) -> -. ps )

  proof
    wps
    wph
    wps
    wph
    wn
    #
    wa
    #
    wb
    #
    wps
    @0
    @1
    wb
    @2
    wn
    wps
    @0
    ibar
    wph
    @1
    nbbn
    sylib
    con2i
end
