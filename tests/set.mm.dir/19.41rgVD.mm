include "wal.mm"
include "wi.mm"
include "wex.mm"
include "wa.mm"
include "idn1.mm"
include "pm3.2.mm"
include "com12.mm"
include "a1i.mm"
include "ax-gen.mm"
include "al2im.mm"
include "e0a.mm"
include "e1a.mm"
include "idn2.mm"
include "id.mm"
include "e12.mm"
include "exim.mm"
include "e2.mm"
include "in2.mm"
include "sp.mm"
include "imim2.mm"
include "e11.mm"
include "pm2.04.mm"
include "pm3.31.mm"
include "in1.mm"

theorem 19.41rgVD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( A. x ( ps -> A. x ps ) -> ( ( E. x ph /\ ps ) -> E. x ( ph /\ ps ) ) )

  proof
    wps
    wps
    vx
    wal
    #
    wi
    #
    vx
    wal
    #
    wph
    vx
    wex
    #
    wps
    wa
    wph
    wps
    wa
    #
    vx
    wex
    #
    wi
    #
    @2
    @3
    wps
    @5
    wi
    wi
    #
    @6
    @2
    wps
    @3
    @5
    wi
    #
    wi
    #
    @7
    @2
    @0
    @8
    wi
    @1
    @9
    @2
    @0
    @8
    @2
    @0
    wph
    @4
    wi
    #
    vx
    wal
    #
    @8
    @2
    @0
    @11
    wi
    #
    @0
    @0
    @11
    @2
    @2
    @12
    @2
    idn1
    #
    @1
    wps
    @10
    wi
    #
    wi
    #
    vx
    wal
    @2
    @12
    wi
    @15
    vx
    @14
    @1
    wph
    wps
    @4
    wph
    wps
    pm3.2
    com12
    a1i
    ax-gen
    @1
    wps
    @10
    vx
    al2im
    e0a
    e1a
    @2
    @0
    idn2
    @12
    id
    e12
    wph
    @4
    vx
    exim
    e2
    in2
    @2
    @2
    @1
    @13
    @1
    vx
    sp
    e1a
    @0
    @8
    wps
    imim2
    e11
    wps
    @3
    @5
    pm2.04
    e1a
    @3
    wps
    @5
    pm3.31
    e1a
    in1
end
