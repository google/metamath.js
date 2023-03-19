include "wal.mm"
include "wi.mm"
include "w3a.mm"
include "idn2.mm"
include "simp1.mm"
include "e2.mm"
include "ax-5.mm"
include "idn1.mm"
include "simp2.mm"
include "id.mm"
include "e12.mm"
include "simp3.mm"
include "pm3.2an3.mm"
include "e222.mm"
include "19.26-3an.mm"
include "biimpri.mm"
include "in2.mm"
include "in1.mm"

theorem 19.21a3con13vVD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x

  disjoint ps x
  disjoint ch x
  assert |- ( ( ph -> A. x ph ) -> ( ( ps /\ ph /\ ch ) -> A. x ( ps /\ ph /\ ch ) ) )

  proof
    wph
    wph
    vx
    wal
    #
    wi
    #
    wps
    wph
    wch
    w3a
    #
    @2
    vx
    wal
    #
    wi
    @1
    @2
    @3
    @1
    @2
    wps
    vx
    wal
    #
    @0
    wch
    vx
    wal
    #
    w3a
    #
    @3
    @1
    @2
    @4
    @0
    @5
    @6
    @1
    @2
    wps
    @4
    @1
    @2
    @2
    wps
    @1
    @2
    idn2
    #
    wps
    wph
    wch
    simp1
    e2
    wps
    vx
    ax-5
    e2
    @1
    @1
    @2
    wph
    @0
    @1
    idn1
    @1
    @2
    @2
    wph
    @7
    wps
    wph
    wch
    simp2
    e2
    @1
    id
    e12
    @1
    @2
    wch
    @5
    @1
    @2
    @2
    wch
    @7
    wps
    wph
    wch
    simp3
    e2
    wch
    vx
    ax-5
    e2
    @4
    @0
    @5
    pm3.2an3
    e222
    @3
    @6
    wps
    wph
    wch
    vx
    19.26-3an
    biimpri
    e2
    in2
    in1
end
