include "wal.mm"
include "wi.mm"
include "wex.mm"
include "hba1.mm"
include "alcom.mm"
include "albii.mm"
include "3imtr4i.mm"
include "wn.mm"
include "wb.mm"
include "idn1.mm"
include "ax-11.mm"
include "e1a.mm"
include "sp.mm"
include "hbntal.mm"
include "gen11nv.mm"
include "hbalg.mm"
include "df-ex.mm"
include "imbi1.mm"
include "biimprcd.mm"
include "e10.mm"
include "imbi2.mm"
include "in1.mm"

theorem hbexgVD
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x A. y ( ph -> A. x ph ) -> A. x A. y ( E. y ph -> A. x E. y ph ) )

  proof
    wph
    wph
    vx
    wal
    wi
    #
    vy
    wal
    #
    vx
    wal
    #
    wph
    vy
    wex
    #
    @3
    vx
    wal
    #
    wi
    #
    vy
    wal
    #
    vx
    wal
    @2
    @6
    vx
    @1
    vx
    hba1
    #
    @2
    @5
    vy
    @0
    vx
    wal
    #
    vy
    wal
    #
    @9
    vy
    wal
    @2
    @2
    vy
    wal
    @8
    vy
    hba1
    @0
    vx
    vy
    alcom
    #
    @2
    @9
    vy
    @10
    albii
    3imtr4i
    #
    @2
    @3
    wph
    wn
    #
    vy
    wal
    #
    wn
    #
    vx
    wal
    #
    wi
    #
    @4
    @15
    wb
    #
    @5
    @2
    @14
    @15
    wi
    #
    @3
    @14
    wb
    #
    @16
    @2
    @18
    vx
    wal
    #
    @18
    @2
    @13
    @13
    vx
    wal
    wi
    #
    vx
    wal
    @20
    @2
    @21
    vx
    @7
    @2
    @21
    vy
    wal
    #
    @21
    @2
    @12
    @12
    vx
    wal
    wi
    #
    vy
    wal
    #
    @22
    @2
    @24
    vx
    wal
    #
    @24
    @2
    @23
    vx
    wal
    #
    vy
    wal
    @25
    @2
    @26
    vy
    @11
    @2
    @8
    @26
    @2
    @9
    @8
    @2
    @2
    @9
    @2
    idn1
    @0
    vx
    vy
    ax-11
    e1a
    @8
    vy
    sp
    e1a
    wph
    vx
    hbntal
    e1a
    gen11nv
    @23
    vy
    vx
    ax-11
    e1a
    @24
    vx
    sp
    e1a
    @12
    vx
    vy
    hbalg
    e1a
    @21
    vy
    sp
    e1a
    gen11nv
    @13
    vx
    hbntal
    e1a
    @18
    vx
    sp
    e1a
    wph
    vy
    df-ex
    #
    @19
    @16
    @18
    @3
    @14
    @15
    imbi1
    biimprcd
    e10
    @3
    @14
    vx
    @27
    albii
    @17
    @5
    @16
    @4
    @15
    @3
    imbi2
    biimprcd
    e10
    gen11nv
    gen11nv
    in1
end
