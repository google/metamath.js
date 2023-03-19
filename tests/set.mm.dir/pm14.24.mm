include "weu.mm"
include "cv.mm"
include "wsbc.mm"
include "cio.mm"
include "wceq.mm"
include "wb.mm"
include "weq.mm"
include "wal.mm"
include "nfeu1.mm"
include "nfsbc1v.mm"
include "wa.mm"
include "wi.mm"
include "pm14.12.mm"
include "19.21bbi.mm"
include "ancomsd.mm"
include "expdimp.mm"
include "pm13.13b.mm"
include "ex.mm"
include "adantl.mm"
include "impbid.mm"
include "alrimd.mm"
include "iotaval.mm"
include "eqcomd.mm"
include "syl6.mm"
include "iota4.mm"
include "dfsbcq.mm"
include "syl5ibrcom.mm"
include "alrimiv.mm"

theorem pm14.24
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  disjoint ph y
  assert |- ( E! x ph -> A. y ( [. y / x ]. ph <-> y = ( iota x ph ) ) )

  proof
    wph
    vx
    weu
    #
    wph
    vx
    vy
    cv
    #
    wsbc
    #
    @1
    wph
    vx
    cio
    #
    wceq
    #
    wb
    vy
    @0
    @2
    @4
    @0
    @2
    wph
    vx
    vy
    weq
    #
    wb
    #
    vx
    wal
    #
    @4
    @0
    @2
    @6
    vx
    wph
    vx
    nfeu1
    wph
    vx
    @1
    nfsbc1v
    @0
    @2
    @6
    @0
    @2
    wa
    wph
    @5
    @0
    @2
    wph
    @5
    @0
    wph
    @2
    @5
    @0
    wph
    @2
    wa
    @5
    wi
    vx
    vy
    wph
    vx
    vy
    pm14.12
    19.21bbi
    ancomsd
    expdimp
    @2
    @5
    wph
    wi
    @0
    @2
    @5
    wph
    wph
    vx
    @1
    pm13.13b
    ex
    adantl
    impbid
    ex
    alrimd
    @7
    @3
    @1
    wph
    vx
    vy
    iotaval
    eqcomd
    syl6
    @0
    @2
    @4
    wph
    vx
    @3
    wsbc
    wph
    vx
    iota4
    wph
    vx
    @1
    @3
    dfsbcq
    syl5ibrcom
    impbid
    alrimiv
end
