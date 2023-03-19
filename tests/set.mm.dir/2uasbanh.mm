include "weq.mm"
include "wa.mm"
include "wex.mm"
include "simpl.mm"
include "simprl.mm"
include "jca.mm"
include "2eximi.mm"
include "simprr.mm"
include "wsb.mm"
include "simplbi.mm"
include "wal.mm"
include "wn.mm"
include "wo.mm"
include "wb.mm"
include "syl.mm"
include "ax6e2ndeq.mm"
include "sylibr.mm"
include "2sb5nd.mm"
include "mpbird.mm"
include "simprbi.mm"
include "sban.mm"
include "sbbii.mm"
include "bitri.mm"
include "sylanbrc.mm"
include "mpbid.mm"
include "sylbir.mm"
include "impbii.mm"

theorem 2uasbanh
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  assume 2uasbanh.1: |- ( ch <-> ( E. x E. y ( ( x = u /\ y = v ) /\ ph ) /\ E. x E. y ( ( x = u /\ y = v ) /\ ps ) ) )

  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  assert |- ( E. x E. y ( ( x = u /\ y = v ) /\ ( ph /\ ps ) ) <-> ( E. x E. y ( ( x = u /\ y = v ) /\ ph ) /\ E. x E. y ( ( x = u /\ y = v ) /\ ps ) ) )

  proof
    vx
    vu
    weq
    vy
    vv
    weq
    wa
    #
    wph
    wps
    wa
    #
    wa
    #
    vy
    wex
    vx
    wex
    #
    @0
    wph
    wa
    #
    vy
    wex
    vx
    wex
    #
    @0
    wps
    wa
    #
    vy
    wex
    vx
    wex
    #
    wa
    #
    @3
    @5
    @7
    @2
    @4
    vx
    vy
    @2
    @0
    wph
    @0
    @1
    simpl
    #
    @0
    wph
    wps
    simprl
    jca
    2eximi
    @2
    @6
    vx
    vy
    @2
    @0
    wps
    @9
    @0
    wph
    wps
    simprr
    jca
    2eximi
    jca
    @8
    wch
    @3
    2uasbanh.1
    wch
    @1
    vy
    vv
    wsb
    #
    vx
    vu
    wsb
    #
    @3
    wch
    wph
    vy
    vv
    wsb
    #
    vx
    vu
    wsb
    #
    wps
    vy
    vv
    wsb
    #
    vx
    vu
    wsb
    #
    @11
    wch
    @13
    @5
    wch
    @5
    @7
    2uasbanh.1
    simplbi
    #
    wch
    vx
    vy
    weq
    vx
    wal
    wn
    vu
    vv
    weq
    wo
    #
    @13
    @5
    wb
    wch
    @0
    vy
    wex
    vx
    wex
    #
    @17
    wch
    @5
    @18
    @16
    @4
    @0
    vx
    vy
    @0
    wph
    simpl
    2eximi
    syl
    vx
    vy
    vv
    vu
    ax6e2ndeq
    sylibr
    #
    wph
    vx
    vy
    vv
    vu
    2sb5nd
    syl
    mpbird
    wch
    @15
    @7
    wch
    @5
    @7
    2uasbanh.1
    simprbi
    wch
    @17
    @15
    @7
    wb
    @19
    wps
    vx
    vy
    vv
    vu
    2sb5nd
    syl
    mpbird
    @11
    @12
    @14
    wa
    #
    vx
    vu
    wsb
    @13
    @15
    wa
    @10
    @20
    vx
    vu
    wph
    wps
    vy
    vv
    sban
    sbbii
    @12
    @14
    vx
    vu
    sban
    bitri
    sylanbrc
    wch
    @17
    @11
    @3
    wb
    @19
    @1
    vx
    vy
    vv
    vu
    2sb5nd
    syl
    mpbid
    sylbir
    impbii
end
