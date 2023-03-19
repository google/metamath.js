include "crio.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cio.mm"
include "df-riota.mm"
include "weq.mm"
include "wal.mm"
include "wnfc.mm"
include "wn.mm"
include "nfnae.mm"
include "nfan.mm"
include "nfcvf.mm"
include "adantl.mm"
include "adantr.mm"
include "nfeld.mm"
include "wnf.mm"
include "nfand.mm"
include "nfiotad.mm"
include "ex.mm"
include "nfiota1.mm"
include "eqidd.mm"
include "drnfc1.mm"
include "mpbiri.mm"
include "pm2.61d2.mm"
include "nfcxfrd.mm"

theorem nfriotad
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume nfriotad.1: |- F/ y ph
  assume nfriotad.2: |- ( ph -> F/ x ps )
  assume nfriotad.3: |- ( ph -> F/_ x A )


  assert |- ( ph -> F/_ x ( iota_ y e. A ps ) )

  proof
    wph
    vx
    wps
    vy
    cA
    crio
    vy
    cv
    #
    cA
    wcel
    #
    wps
    wa
    #
    vy
    cio
    #
    wps
    vy
    cA
    df-riota
    wph
    vx
    vy
    weq
    vx
    wal
    #
    vx
    @3
    wnfc
    #
    wph
    @4
    wn
    #
    @5
    wph
    @6
    wa
    #
    @2
    vx
    vy
    wph
    @6
    vy
    nfriotad.1
    vx
    vy
    vy
    nfnae
    nfan
    @7
    @1
    wps
    vx
    @7
    vx
    @0
    cA
    @6
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
    @6
    nfriotad.3
    adantr
    nfeld
    wph
    wps
    vx
    wnf
    @6
    nfriotad.2
    adantr
    nfand
    nfiotad
    ex
    @4
    @5
    vy
    @3
    wnfc
    @2
    vy
    nfiota1
    vx
    vy
    @3
    @3
    @4
    @3
    eqidd
    drnfc1
    mpbiri
    pm2.61d2
    nfcxfrd
end
