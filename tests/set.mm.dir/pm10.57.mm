include "wo.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wex.mm"
include "wn.mm"
include "alnex.mm"
include "imnan.mm"
include "pm2.53.mm"
include "con1d.mm"
include "imim3i.mm"
include "syl5bir.mm"
include "al2imi.mm"
include "orrd.mm"

theorem pm10.57
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x


  assert |- ( A. x ( ph -> ( ps \/ ch ) ) -> ( A. x ( ph -> ps ) \/ E. x ( ph /\ ch ) ) )

  proof
    wph
    wps
    wch
    wo
    #
    wi
    #
    vx
    wal
    #
    wph
    wps
    wi
    #
    vx
    wal
    #
    wph
    wch
    wa
    #
    vx
    wex
    #
    @2
    @6
    @4
    @6
    wn
    @5
    wn
    #
    vx
    wal
    @2
    @4
    @5
    vx
    alnex
    @1
    @7
    @3
    vx
    @7
    wph
    wch
    wn
    #
    wi
    @1
    @3
    wph
    wch
    imnan
    @0
    @8
    wps
    wph
    @0
    wps
    wch
    wps
    wch
    pm2.53
    con1d
    imim3i
    syl5bir
    al2imi
    syl5bir
    con1d
    orrd
end
