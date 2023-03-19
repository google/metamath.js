include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "csb.mm"
include "wsbc.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfcri.mm"
include "nfsbc1v.mm"
include "nfim.mm"
include "weq.mm"
include "id.mm"
include "csbeq1a.mm"
include "eleq12d.mm"
include "sbceq1a.mm"
include "imbi12d.mm"
include "cbval.mm"
include "nfcv.mm"
include "nfcsb.mm"
include "nfsbc.mm"
include "csbeq1.mm"
include "cab.mm"
include "df-csb.mm"
include "wsb.mm"
include "eleq2d.mm"
include "sbie.mm"
include "sbsbc.mm"
include "bitr3i.mm"
include "abbi2i.mm"
include "eqtr4i.mm"
include "syl6eq.mm"
include "dfsbcq.mm"
include "syl6bb.mm"
include "bitri.mm"
include "df-ral.mm"
include "3bitr4i.mm"

theorem cbvralcsf
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vv: setvar v
  let vz: setvar z
  assume cbvralcsf.1: |- F/_ y A
  assume cbvralcsf.2: |- F/_ x B
  assume cbvralcsf.3: |- F/ y ph
  assume cbvralcsf.4: |- F/ x ps
  assume cbvralcsf.5: |- ( x = y -> A = B )
  assume cbvralcsf.6: |- ( x = y -> ( ph <-> ps ) )


  assert |- ( A. x e. A ph <-> A. y e. B ps )

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
    cB
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
    cB
    wral
    @3
    vz
    cv
    #
    vx
    @8
    cA
    csb
    #
    wcel
    #
    wph
    vx
    @8
    wsbc
    #
    wi
    #
    vz
    wal
    @7
    @2
    @12
    vx
    vz
    @2
    vz
    nfv
    @10
    @11
    vx
    vx
    vz
    @9
    vx
    @8
    cA
    nfcsb1v
    nfcri
    wph
    vx
    @8
    nfsbc1v
    nfim
    vx
    vz
    weq
    #
    @1
    @10
    wph
    @11
    @13
    @0
    @8
    cA
    @9
    @13
    id
    vx
    @8
    cA
    csbeq1a
    eleq12d
    wph
    vx
    @8
    sbceq1a
    imbi12d
    cbval
    @12
    @6
    vz
    vy
    @10
    @11
    vy
    vy
    vz
    @9
    vy
    vx
    @8
    cA
    vy
    @8
    nfcv
    #
    cbvralcsf.1
    nfcsb
    nfcri
    wph
    vy
    vx
    @8
    @14
    cbvralcsf.3
    nfsbc
    nfim
    @6
    vz
    nfv
    vz
    vy
    weq
    #
    @10
    @5
    @11
    wps
    @15
    @8
    @4
    @9
    cB
    @15
    id
    @15
    @9
    vx
    @4
    cA
    csb
    #
    cB
    vx
    @8
    @4
    cA
    csbeq1
    @16
    vv
    cv
    #
    cA
    wcel
    #
    vx
    @4
    wsbc
    #
    vv
    cab
    cB
    vx
    vv
    @4
    cA
    df-csb
    @19
    vv
    cB
    @17
    cB
    wcel
    #
    @18
    vx
    vy
    wsb
    @19
    @18
    @20
    vx
    vy
    vx
    vv
    cB
    cbvralcsf.2
    nfcri
    vx
    vy
    weq
    cA
    cB
    @17
    cbvralcsf.5
    eleq2d
    sbie
    @18
    vx
    vy
    sbsbc
    bitr3i
    abbi2i
    eqtr4i
    syl6eq
    eleq12d
    @15
    @11
    wph
    vx
    @4
    wsbc
    #
    wps
    wph
    vx
    @8
    @4
    dfsbcq
    @21
    wph
    vx
    vy
    wsb
    wps
    wph
    vx
    vy
    sbsbc
    wph
    wps
    vx
    vy
    cbvralcsf.4
    cbvralcsf.6
    sbie
    bitr3i
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
    cB
    df-ral
    3bitr4i
end
