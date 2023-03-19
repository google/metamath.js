include "wa.mm"
include "wi.mm"
include "wal.mm"
include "pm3.3.mm"
include "alimi.mm"
include "al2im.mm"
include "syl.mm"
include "impd.mm"

theorem bj-alanim
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x


  assert |- ( A. x ( ( ph /\ ps ) -> ch ) -> ( ( A. x ph /\ A. x ps ) -> A. x ch ) )

  proof
    wph
    wps
    wa
    wch
    wi
    #
    vx
    wal
    #
    wph
    vx
    wal
    #
    wps
    vx
    wal
    #
    wch
    vx
    wal
    #
    @1
    wph
    wps
    wch
    wi
    wi
    #
    vx
    wal
    @2
    @3
    @4
    wi
    wi
    @0
    @5
    vx
    wph
    wps
    wch
    pm3.3
    alimi
    wph
    wps
    wch
    vx
    al2im
    syl
    impd
end
