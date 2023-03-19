include "wex.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wal.mm"
include "wi.mm"
include "ianor.mm"
include "alnex.mm"
include "pm2.53.mm"
include "al2imi.mm"
include "syl5bir.mm"
include "olc.mm"
include "syl6com.mm"
include "19.30.mm"
include "orcomd.mm"
include "ord.mm"
include "orc.mm"
include "jaoi.mm"
include "sylbi.mm"
include "19.33.mm"
include "impbid1.mm"

theorem 19.33b
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( -. ( E. x ph /\ E. x ps ) -> ( A. x ( ph \/ ps ) <-> ( A. x ph \/ A. x ps ) ) )

  proof
    wph
    vx
    wex
    #
    wps
    vx
    wex
    #
    wa
    wn
    #
    wph
    wps
    wo
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
    wo
    #
    @2
    @0
    wn
    #
    @1
    wn
    #
    wo
    @4
    @7
    wi
    #
    @0
    @1
    ianor
    @8
    @10
    @9
    @4
    @8
    @6
    @7
    @8
    wph
    wn
    #
    vx
    wal
    @4
    @6
    wph
    vx
    alnex
    @3
    @11
    wps
    vx
    wph
    wps
    pm2.53
    al2imi
    syl5bir
    @6
    @5
    olc
    syl6com
    @4
    @9
    @5
    @7
    @4
    @1
    @5
    @4
    @5
    @1
    wph
    wps
    vx
    19.30
    orcomd
    ord
    @5
    @6
    orc
    syl6com
    jaoi
    sylbi
    wph
    wps
    vx
    19.33
    impbid1
end
