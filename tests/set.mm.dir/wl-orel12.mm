include "wo.mm"
include "wn.mm"
include "wa.mm"
include "pm2.1.mm"
include "orel1.mm"
include "orc.mm"
include "syl6com.mm"
include "wi.mm"
include "notnot.mm"
include "syl.mm"
include "olc.mm"
include "jaao.mm"
include "mpi.mm"

theorem wl-orel12
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph \/ ps ) /\ ( -. ph \/ ch ) ) -> ( ps \/ ch ) )

  proof
    wph
    wps
    wo
    #
    wph
    wn
    #
    wch
    wo
    #
    wa
    @1
    wph
    wo
    wps
    wch
    wo
    #
    wph
    pm2.1
    @0
    @1
    @3
    @2
    wph
    @1
    @0
    wps
    @3
    wph
    wps
    orel1
    wps
    wch
    orc
    syl6com
    wph
    @2
    wch
    @3
    wph
    @1
    wn
    @2
    wch
    wi
    wph
    notnot
    @1
    wch
    orel1
    syl
    wch
    wps
    olc
    syl6com
    jaao
    mpi
end
