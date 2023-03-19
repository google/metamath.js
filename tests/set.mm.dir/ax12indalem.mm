include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wi.mm"
include "ax-1.mm"
include "axc4i-o.mm"
include "a1i.mm"
include "biidd.mm"
include "dral1-o.mm"
include "imbi2d.mm"
include "dral2-o.mm"
include "3imtr4d.mm"
include "aecoms-o.mm"
include "a1d.mm"
include "adantr.mm"
include "wa.mm"
include "simplr.mm"
include "aecom-o.mm"
include "con3i.mm"
include "axc9.mm"
include "imp.mm"
include "syl2an.mm"
include "adantlr.mm"
include "hbnae-o.mm"
include "hba1-o.mm"
include "hban.mm"
include "ax-c5.mm"
include "sylan2.mm"
include "alimdh.mm"
include "syl2anc.mm"
include "ax-11.mm"
include "wnf.mm"
include "wb.mm"
include "nf5dh.mm"
include "19.21t.mm"
include "syl.mm"
include "albidh.mm"
include "syl5ib.mm"
include "ad2antrr.mm"
include "syld.mm"
include "exp31.mm"
include "pm2.61ian.mm"

theorem ax12indalem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ax12indalem.1: |- ( -. A. x x = y -> ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) )


  assert |- ( -. A. y y = z -> ( -. A. x x = y -> ( x = y -> ( A. z ph -> A. x ( x = y -> A. z ph ) ) ) ) )

  proof
    vx
    vz
    weq
    vx
    wal
    #
    vy
    vz
    weq
    vy
    wal
    #
    wn
    #
    vx
    vy
    weq
    #
    vx
    wal
    wn
    #
    @3
    wph
    vz
    wal
    #
    @3
    @5
    wi
    #
    vx
    wal
    #
    wi
    #
    wi
    #
    wi
    #
    @0
    @10
    @2
    @0
    @9
    @4
    @0
    @8
    @3
    @8
    vz
    vx
    vz
    vx
    weq
    vz
    wal
    #
    wph
    vx
    wal
    #
    @3
    @12
    wi
    #
    vx
    wal
    #
    @5
    @7
    @12
    @14
    wi
    @11
    wph
    @13
    vx
    @12
    @3
    ax-1
    axc4i-o
    a1i
    wph
    wph
    vz
    vx
    @11
    wph
    biidd
    dral1-o
    #
    @6
    @13
    vz
    vx
    vx
    @11
    @5
    @12
    @3
    @15
    imbi2d
    dral2-o
    3imtr4d
    aecoms-o
    a1d
    a1d
    adantr
    @0
    wn
    #
    @2
    wa
    #
    @4
    @3
    @8
    @17
    @4
    wa
    @3
    wa
    #
    @5
    @3
    wph
    wi
    #
    vx
    wal
    #
    vz
    wal
    #
    @7
    @18
    @4
    @3
    vz
    wal
    #
    @5
    @21
    wi
    @17
    @4
    @3
    simplr
    @17
    @3
    @22
    @4
    @17
    @3
    @22
    @16
    @11
    wn
    #
    vz
    vy
    weq
    vz
    wal
    #
    wn
    #
    @3
    @22
    wi
    #
    @2
    @11
    @0
    vz
    vx
    aecom-o
    con3i
    @24
    @1
    vz
    vy
    aecom-o
    con3i
    @23
    @25
    @26
    vx
    vy
    vz
    axc9
    imp
    syl2an
    #
    imp
    adantlr
    @4
    @22
    wa
    wph
    @20
    vz
    @4
    @22
    vz
    vx
    vy
    vz
    hbnae-o
    @3
    vz
    hba1-o
    hban
    @22
    @4
    @3
    wph
    @20
    wi
    #
    @3
    vz
    ax-c5
    @4
    @3
    @28
    ax12indalem.1
    imp
    sylan2
    alimdh
    syl2anc
    @17
    @21
    @7
    wi
    @4
    @3
    @21
    @19
    vz
    wal
    #
    vx
    wal
    @17
    @7
    @19
    vz
    vx
    ax-11
    @17
    @29
    @6
    vx
    @16
    @2
    vx
    vx
    vz
    vx
    hbnae-o
    vy
    vz
    vx
    hbnae-o
    hban
    @17
    @3
    vz
    wnf
    @29
    @6
    wb
    @17
    @3
    vz
    @16
    @2
    vz
    vx
    vz
    vz
    hbnae-o
    vy
    vz
    vz
    hbnae-o
    hban
    @27
    nf5dh
    @3
    wph
    vz
    19.21t
    syl
    albidh
    syl5ib
    ad2antrr
    syld
    exp31
    pm2.61ian
end
