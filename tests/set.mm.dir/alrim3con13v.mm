include "wal.mm"
include "wi.mm"
include "w3a.mm"
include "simp1.mm"
include "a1i.mm"
include "ax-5.mm"
include "syl6.mm"
include "simp2.mm"
include "imim1i.mm"
include "simp3.mm"
include "3jcad.mm"
include "19.26-3an.mm"
include "syl6ibr.mm"

theorem alrim3con13v
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
    @2
    vx
    wal
    @1
    @2
    @3
    @0
    @4
    @1
    @2
    wps
    @3
    @2
    wps
    wi
    @1
    wps
    wph
    wch
    simp1
    a1i
    wps
    vx
    ax-5
    syl6
    @2
    wph
    @0
    wps
    wph
    wch
    simp2
    imim1i
    @1
    @2
    wch
    @4
    @2
    wch
    wi
    @1
    wps
    wph
    wch
    simp3
    a1i
    wch
    vx
    ax-5
    syl6
    3jcad
    wps
    wph
    wch
    vx
    19.26-3an
    syl6ibr
end
