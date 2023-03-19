include "wal.mm"
include "wi.mm"
include "wa.mm"
include "hba1.mm"
include "hban.mm"
include "wn.mm"
include "wo.mm"
include "wb.mm"
include "idn2.mm"
include "idn1.mm"
include "simpl.mm"
include "e1a.mm"
include "hbntal.mm"
include "sp.mm"
include "pm2.27.mm"
include "e21.mm"
include "pm2.21.mm"
include "alimi.mm"
include "e2.mm"
include "in2.mm"
include "simpr.mm"
include "ax-1.mm"
include "imim1.mm"
include "e10.mm"
include "jao.mm"
include "e11.mm"
include "imor.mm"
include "imbi1.mm"
include "biimprcd.mm"
include "gen11nv.mm"
include "in1.mm"

theorem hbimpgVD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( ( A. x ( ph -> A. x ph ) /\ A. x ( ps -> A. x ps ) ) -> A. x ( ( ph -> ps ) -> A. x ( ph -> ps ) ) )

  proof
    wph
    wph
    vx
    wal
    wi
    #
    vx
    wal
    #
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
    wa
    #
    wph
    wps
    wi
    #
    @6
    vx
    wal
    #
    wi
    #
    vx
    wal
    @5
    @8
    vx
    @1
    @4
    vx
    @0
    vx
    hba1
    @3
    vx
    hba1
    hban
    @5
    wph
    wn
    #
    wps
    wo
    #
    @7
    wi
    #
    @6
    @10
    wb
    #
    @8
    @5
    @9
    @7
    wi
    wps
    @7
    wi
    #
    @11
    @5
    @9
    @7
    @5
    @9
    @9
    vx
    wal
    #
    @7
    @5
    @9
    @9
    @9
    @14
    wi
    #
    @14
    @5
    @9
    idn2
    @5
    @15
    vx
    wal
    #
    @15
    @5
    @1
    @16
    @5
    @5
    @1
    @5
    idn1
    #
    @1
    @4
    simpl
    e1a
    wph
    vx
    hbntal
    e1a
    @15
    vx
    sp
    e1a
    @9
    @14
    pm2.27
    e21
    @9
    @6
    vx
    wph
    wps
    pm2.21
    alimi
    e2
    in2
    @5
    @3
    @2
    @7
    wi
    @13
    @5
    @4
    @3
    @5
    @5
    @4
    @17
    @1
    @4
    simpr
    e1a
    @3
    vx
    sp
    e1a
    wps
    @6
    vx
    wps
    wph
    ax-1
    alimi
    wps
    @2
    @7
    imim1
    e10
    @9
    @7
    wps
    jao
    e11
    wph
    wps
    imor
    @12
    @8
    @11
    @6
    @10
    @7
    imbi1
    biimprcd
    e10
    gen11nv
    in1
end
