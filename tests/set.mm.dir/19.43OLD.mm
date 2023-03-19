include "wo.mm"
include "wn.mm"
include "wal.mm"
include "wex.mm"
include "wa.mm"
include "ioran.mm"
include "albii.mm"
include "19.26.mm"
include "alnex.mm"
include "anbi12i.mm"
include "3bitri.mm"
include "notbii.mm"
include "df-ex.mm"
include "oran.mm"
include "3bitr4i.mm"

theorem 19.43OLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( E. x ( ph \/ ps ) <-> ( E. x ph \/ E. x ps ) )

  proof
    wph
    wps
    wo
    #
    wn
    #
    vx
    wal
    #
    wn
    wph
    vx
    wex
    #
    wn
    #
    wps
    vx
    wex
    #
    wn
    #
    wa
    #
    wn
    @0
    vx
    wex
    @3
    @5
    wo
    @2
    @7
    @2
    wph
    wn
    #
    wps
    wn
    #
    wa
    #
    vx
    wal
    @8
    vx
    wal
    #
    @9
    vx
    wal
    #
    wa
    @7
    @1
    @10
    vx
    wph
    wps
    ioran
    albii
    @8
    @9
    vx
    19.26
    @11
    @4
    @12
    @6
    wph
    vx
    alnex
    wps
    vx
    alnex
    anbi12i
    3bitri
    notbii
    @0
    vx
    df-ex
    @3
    @5
    oran
    3bitr4i
end
