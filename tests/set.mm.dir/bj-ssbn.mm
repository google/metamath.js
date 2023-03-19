include "wn.mm"
include "wssb.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wex.mm"
include "df-ssb.mm"
include "alinexa.mm"
include "imbi2i.mm"
include "albii.mm"
include "bj-dfssb2.mm"
include "xchbinxr.mm"
include "3bitri.mm"

theorem bj-ssbn
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let vy: setvar y


  assert |- ( [b t /b x ]b -. ph <-> -. [b t /b x ]b ph )

  proof
    wph
    wn
    #
    vx
    vt
    wssb
    vy
    vt
    weq
    #
    vx
    vy
    weq
    #
    @0
    wi
    vx
    wal
    #
    wi
    #
    vy
    wal
    @1
    @2
    wph
    wa
    vx
    wex
    #
    wn
    #
    wi
    #
    vy
    wal
    #
    wph
    vx
    vt
    wssb
    #
    wn
    @0
    vx
    vy
    vt
    df-ssb
    @4
    @7
    vy
    @3
    @6
    @1
    @2
    wph
    vx
    alinexa
    imbi2i
    albii
    @8
    @1
    @5
    wa
    vy
    wex
    @9
    @1
    @5
    vy
    alinexa
    wph
    vx
    vy
    vt
    bj-dfssb2
    xchbinxr
    3bitri
end
