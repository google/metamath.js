include "cio.mm"
include "weq.mm"
include "wb.mm"
include "wal.mm"
include "cab.mm"
include "cuni.mm"
include "dfiota2.mm"
include "nfv.mm"
include "wn.mm"
include "wa.mm"
include "wnf.mm"
include "adantr.mm"
include "nfeqf1.mm"
include "adantl.mm"
include "nfbid.mm"
include "nfald2.mm"
include "nfabd.mm"
include "nfunid.mm"
include "nfcxfrd.mm"

theorem nfiotad
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume nfiotad.1: |- F/ y ph
  assume nfiotad.2: |- ( ph -> F/ x ps )


  assert |- ( ph -> F/_ x ( iota y ps ) )

  proof
    wph
    vx
    wps
    vy
    cio
    wps
    vy
    vz
    weq
    #
    wb
    #
    vy
    wal
    #
    vz
    cab
    #
    cuni
    wps
    vy
    vz
    dfiota2
    wph
    vx
    @3
    wph
    @2
    vx
    vz
    wph
    vz
    nfv
    wph
    @1
    vx
    vy
    nfiotad.1
    wph
    vx
    vy
    weq
    vx
    wal
    wn
    #
    wa
    wps
    @0
    vx
    wph
    wps
    vx
    wnf
    @4
    nfiotad.2
    adantr
    @4
    @0
    vx
    wnf
    wph
    vx
    vy
    vz
    nfeqf1
    adantl
    nfbid
    nfald2
    nfabd
    nfunid
    nfcxfrd
end
