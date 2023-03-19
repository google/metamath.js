include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wa.mm"
include "wsb.mm"
include "wi.mm"
include "wb.mm"
include "jca.mm"
include "wl-sb6nae.mm"
include "nfnae.mm"
include "wl-nfnae1.mm"
include "nfan.mm"
include "imbi2d.mm"
include "impexp.mm"
include "albii.mm"
include "wnf.mm"
include "nfeqf.mm"
include "19.21t.mm"
include "syl.mm"
include "syl5rbb.mm"
include "sylan9bb.mm"
include "albid.mm"
include "syl12anc.mm"

theorem wl-2sb6d
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume wl-2sb6d.1: |- ( ph -> -. A. y y = x )
  assume wl-2sb6d.2: |- ( ph -> -. A. y y = w )
  assume wl-2sb6d.3: |- ( ph -> -. A. y y = z )
  assume wl-2sb6d.4: |- ( ph -> -. A. x x = z )


  assert |- ( ph -> ( [ z / x ] [ w / y ] ps <-> A. x A. y ( ( x = z /\ y = w ) -> ps ) ) )

  proof
    wph
    vx
    vz
    weq
    #
    vx
    wal
    wn
    #
    vy
    vw
    weq
    #
    vy
    wal
    wn
    #
    vy
    vx
    weq
    vy
    wal
    wn
    #
    vy
    vz
    weq
    vy
    wal
    wn
    #
    wa
    #
    wps
    vy
    vw
    wsb
    #
    vx
    vz
    wsb
    #
    @0
    @2
    wa
    wps
    wi
    #
    vy
    wal
    #
    vx
    wal
    #
    wb
    wl-2sb6d.4
    wl-2sb6d.2
    wph
    @4
    @5
    wl-2sb6d.1
    wl-2sb6d.3
    jca
    @1
    @8
    @0
    @7
    wi
    #
    vx
    wal
    @3
    @6
    wa
    #
    @11
    @7
    vx
    vz
    wl-sb6nae
    @13
    @12
    @10
    vx
    @3
    @6
    vx
    vy
    vw
    vx
    nfnae
    @4
    @5
    vx
    vx
    vy
    wl-nfnae1
    vy
    vz
    vx
    nfnae
    nfan
    nfan
    @3
    @12
    @0
    @2
    wps
    wi
    #
    vy
    wal
    #
    wi
    #
    @6
    @10
    @3
    @7
    @15
    @0
    wps
    vy
    vw
    wl-sb6nae
    imbi2d
    @10
    @0
    @14
    wi
    #
    vy
    wal
    #
    @6
    @16
    @9
    @17
    vy
    @0
    @2
    wps
    impexp
    albii
    @6
    @0
    vy
    wnf
    @18
    @16
    wb
    vx
    vz
    vy
    nfeqf
    @0
    @14
    vy
    19.21t
    syl
    syl5rbb
    sylan9bb
    albid
    sylan9bb
    syl12anc
end
