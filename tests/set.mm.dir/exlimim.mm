include "wi.mm"
include "wal.mm"
include "wex.mm"
include "nfa1.mm"
include "nfv.mm"
include "sp.mm"
include "exlimd.mm"
include "impcom.mm"

theorem exlimim
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x

  disjoint ps x
  assert |- ( ( E. x ph /\ A. x ( ph -> ps ) ) -> ps )

  proof
    wph
    wps
    wi
    #
    vx
    wal
    #
    wph
    vx
    wex
    wps
    @1
    wph
    wps
    vx
    @0
    vx
    nfa1
    wps
    vx
    nfv
    @0
    vx
    sp
    exlimd
    impcom
end
