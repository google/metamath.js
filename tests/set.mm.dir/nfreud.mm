include "wreu.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "weu.mm"
include "df-reu.mm"
include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wnfc.mm"
include "nfcvf.mm"
include "adantl.mm"
include "adantr.mm"
include "nfeld.mm"
include "wnf.mm"
include "nfand.mm"
include "nfeud2.mm"
include "nfxfrd.mm"

theorem nfreud
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume nfreud.1: |- F/ y ph
  assume nfreud.2: |- ( ph -> F/_ x A )
  assume nfreud.3: |- ( ph -> F/ x ps )


  assert |- ( ph -> F/ x E! y e. A ps )

  proof
    wps
    vy
    cA
    wreu
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
    weu
    wph
    vx
    wps
    vy
    cA
    df-reu
    wph
    @2
    vx
    vy
    nfreud.1
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
    nfreud.2
    adantr
    nfeld
    wph
    wps
    vx
    wnf
    @3
    nfreud.3
    adantr
    nfand
    nfeud2
    nfxfrd
end
