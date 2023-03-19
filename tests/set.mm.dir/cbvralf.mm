include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "wsb.mm"
include "nfv.mm"
include "nfcri.mm"
include "nfs1v.mm"
include "nfim.mm"
include "weq.mm"
include "eleq1.mm"
include "sbequ12.mm"
include "imbi12d.mm"
include "cbval.mm"
include "nfsb.mm"
include "sbequ.mm"
include "sbie.mm"
include "syl6bb.mm"
include "bitri.mm"
include "df-ral.mm"
include "3bitr4i.mm"

theorem cbvralf
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  assume cbvralf.1: |- F/_ x A
  assume cbvralf.2: |- F/_ y A
  assume cbvralf.3: |- F/ y ph
  assume cbvralf.4: |- F/ x ps
  assume cbvralf.5: |- ( x = y -> ( ph <-> ps ) )


  assert |- ( A. x e. A ph <-> A. y e. A ps )

  proof
    vx
    cv
    #
    cA
    wcel
    #
    wph
    wi
    #
    vx
    wal
    #
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
    #
    wph
    vx
    cA
    wral
    wps
    vy
    cA
    wral
    @3
    vz
    cv
    #
    cA
    wcel
    #
    wph
    vx
    vz
    wsb
    #
    wi
    #
    vz
    wal
    @7
    @2
    @11
    vx
    vz
    @2
    vz
    nfv
    @9
    @10
    vx
    vx
    vz
    cA
    cbvralf.1
    nfcri
    wph
    vx
    vz
    nfs1v
    nfim
    vx
    vz
    weq
    @1
    @9
    wph
    @10
    @0
    @8
    cA
    eleq1
    wph
    vx
    vz
    sbequ12
    imbi12d
    cbval
    @11
    @6
    vz
    vy
    @9
    @10
    vy
    vy
    vz
    cA
    cbvralf.2
    nfcri
    wph
    vx
    vz
    vy
    cbvralf.3
    nfsb
    nfim
    @6
    vz
    nfv
    vz
    vy
    weq
    #
    @9
    @5
    @10
    wps
    @8
    @4
    cA
    eleq1
    @12
    @10
    wph
    vx
    vy
    wsb
    wps
    wph
    vz
    vy
    vx
    sbequ
    wph
    wps
    vx
    vy
    cbvralf.4
    cbvralf.5
    sbie
    syl6bb
    imbi12d
    cbval
    bitri
    wph
    vx
    cA
    df-ral
    wps
    vy
    cA
    df-ral
    3bitr4i
end
