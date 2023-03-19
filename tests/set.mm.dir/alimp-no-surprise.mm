include "wi.mm"
include "wn.mm"
include "wa.mm"
include "wal.mm"
include "wex.mm"
include "w3a.mm"
include "pm4.82.mm"
include "albii.mm"
include "alnex.mm"
include "sylbb.mm"
include "imnan.mm"
include "mpbi.mm"
include "19.26.mm"
include "anbi2ci.mm"
include "3anass.mm"
include "3anrot.mm"
include "3bitr2i.mm"
include "mtbi.mm"

theorem alimp-no-surprise
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vk: setvar k


  assert |- -. ( A. x ( ph -> ps ) /\ A. x ( ph -> -. ps ) /\ E. x ph )

  proof
    wph
    wps
    wi
    #
    wph
    wps
    wn
    wi
    #
    wa
    #
    vx
    wal
    #
    wph
    vx
    wex
    #
    wa
    #
    @0
    vx
    wal
    #
    @1
    vx
    wal
    #
    @4
    w3a
    #
    @3
    @4
    wn
    #
    wi
    @5
    wn
    @3
    wph
    wn
    #
    vx
    wal
    @9
    @2
    @10
    vx
    wph
    wps
    pm4.82
    albii
    wph
    vx
    alnex
    sylbb
    @3
    @4
    imnan
    mpbi
    @5
    @4
    @6
    @7
    wa
    #
    wa
    @4
    @6
    @7
    w3a
    @8
    @3
    @11
    @4
    @0
    @1
    vx
    19.26
    anbi2ci
    @4
    @6
    @7
    3anass
    @4
    @6
    @7
    3anrot
    3bitr2i
    mtbi
end
