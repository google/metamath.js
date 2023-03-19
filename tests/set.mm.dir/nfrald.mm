include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "df-ral.mm"
include "weq.mm"
include "wn.mm"
include "wa.mm"
include "wnfc.mm"
include "nfcvf.mm"
include "adantl.mm"
include "adantr.mm"
include "nfeld.mm"
include "wnf.mm"
include "nfimd.mm"
include "nfald2.mm"
include "nfxfrd.mm"

theorem nfrald
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume nfrald.1: |- F/ y ph
  assume nfrald.2: |- ( ph -> F/_ x A )
  assume nfrald.3: |- ( ph -> F/ x ps )


  assert |- ( ph -> F/ x A. y e. A ps )

  proof
    wps
    vy
    cA
    wral
    vy
    cv
    #
    cA
    wcel
    #
    wps
    wi
    #
    vy
    wal
    wph
    vx
    wps
    vy
    cA
    df-ral
    wph
    @2
    vx
    vy
    nfrald.1
    wph
    vx
    vy
    weq
    vx
    wal
    wn
    #
    wa
    #
    @1
    wps
    vx
    @4
    vx
    @0
    cA
    @3
    vx
    @0
    wnfc
    wph
    vx
    vy
    nfcvf
    adantl
    wph
    vx
    cA
    wnfc
    @3
    nfrald.2
    adantr
    nfeld
    wph
    wps
    vx
    wnf
    @3
    nfrald.3
    adantr
    nfimd
    nfald2
    nfxfrd
end
