include "weu.mm"
include "cio.mm"
include "wsbc.mm"
include "weq.mm"
include "wb.mm"
include "wal.mm"
include "wa.mm"
include "wex.mm"
include "w3a.mm"
include "iotasbc.mm"
include "anbi2d.mm"
include "3anass.mm"
include "exbii.mm"
include "19.42v.mm"
include "bitr2i.mm"
include "syl6bb.mm"
include "exbidv.mm"
include "sylan9bb.mm"

theorem iotasbc2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint ph y
  disjoint ph z
  disjoint ps y
  disjoint ps z
  assert |- ( ( E! x ph /\ E! x ps ) -> ( [. ( iota x ph ) / y ]. [. ( iota x ps ) / z ]. ch <-> E. y E. z ( A. x ( ph <-> x = y ) /\ A. x ( ps <-> x = z ) /\ ch ) ) )

  proof
    wph
    vx
    weu
    wch
    vz
    wps
    vx
    cio
    wsbc
    #
    vy
    wph
    vx
    cio
    wsbc
    wph
    vx
    vy
    weq
    wb
    vx
    wal
    #
    @0
    wa
    #
    vy
    wex
    wps
    vx
    weu
    #
    @1
    wps
    vx
    vz
    weq
    wb
    vx
    wal
    #
    wch
    w3a
    #
    vz
    wex
    #
    vy
    wex
    wph
    @0
    vx
    vy
    iotasbc
    @3
    @2
    @6
    vy
    @3
    @2
    @1
    @4
    wch
    wa
    #
    vz
    wex
    #
    wa
    #
    @6
    @3
    @0
    @8
    @1
    wps
    wch
    vx
    vz
    iotasbc
    anbi2d
    @6
    @1
    @7
    wa
    #
    vz
    wex
    @9
    @5
    @10
    vz
    @1
    @4
    wch
    3anass
    exbii
    @1
    @7
    vz
    19.42v
    bitr2i
    syl6bb
    exbidv
    sylan9bb
end
