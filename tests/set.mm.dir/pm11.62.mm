include "wa.mm"
include "wi.mm"
include "wal.mm"
include "impexp.mm"
include "albii.mm"
include "19.21v.mm"
include "bitri.mm"

theorem pm11.62
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y

  disjoint ph y
  assert |- ( A. x A. y ( ( ph /\ ps ) -> ch ) <-> A. x ( ph -> A. y ( ps -> ch ) ) )

  proof
    wph
    wps
    wa
    wch
    wi
    #
    vy
    wal
    #
    wph
    wps
    wch
    wi
    #
    vy
    wal
    wi
    #
    vx
    @1
    wph
    @2
    wi
    #
    vy
    wal
    @3
    @0
    @4
    vy
    wph
    wps
    wch
    impexp
    albii
    wph
    @2
    vy
    19.21v
    bitri
    albii
end
