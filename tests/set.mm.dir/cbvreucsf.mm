include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "weu.mm"
include "wreu.mm"
include "csb.mm"
include "wsb.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfcri.mm"
include "nfs1v.mm"
include "nfan.mm"
include "weq.mm"
include "id.mm"
include "csbeq1a.mm"
include "eleq12d.mm"
include "sbequ12.mm"
include "anbi12d.mm"
include "cbveu.mm"
include "nfcv.mm"
include "nfcsb.mm"
include "nfsb.mm"
include "csbeq1.mm"
include "cab.mm"
include "wsbc.mm"
include "sbsbc.mm"
include "abbii.mm"
include "eleq2d.mm"
include "sbie.mm"
include "bicomi.mm"
include "abbi2i.mm"
include "df-csb.mm"
include "3eqtr4ri.mm"
include "syl6eq.mm"
include "sbequ.mm"
include "syl6bb.mm"
include "bitri.mm"
include "df-reu.mm"
include "3bitr4i.mm"

theorem cbvreucsf
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


  assert |- ( E! x e. A ph <-> E! y e. B ps )

  proof
    vx
    cv
    #
    cA
    wcel
    #
    wph
    wa
    #
    vx
    weu
    #
    vy
    cv
    #
    cB
    wcel
    #
    wps
    wa
    #
    vy
    weu
    #
    wph
    vx
    cA
    wreu
    wps
    vy
    cB
    wreu
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
    vz
    wsb
    #
    wa
    #
    vz
    weu
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
    vz
    nfs1v
    nfan
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
    vz
    sbequ12
    anbi12d
    cbveu
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
    cbvralcsf.1
    nfcsb
    nfcri
    wph
    vx
    vz
    vy
    cbvralcsf.3
    nfsb
    nfan
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
    @14
    @8
    @4
    @9
    cB
    @14
    id
    @14
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
    vv
    cv
    #
    cA
    wcel
    #
    vx
    vy
    wsb
    #
    vv
    cab
    @17
    vx
    @4
    wsbc
    #
    vv
    cab
    cB
    @15
    @18
    @19
    vv
    @17
    vx
    vy
    sbsbc
    abbii
    @18
    vv
    cB
    @18
    @16
    cB
    wcel
    #
    @17
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
    @16
    cbvralcsf.5
    eleq2d
    sbie
    bicomi
    abbi2i
    vx
    vv
    @4
    cA
    df-csb
    3eqtr4ri
    syl6eq
    eleq12d
    @14
    @11
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
    cbvralcsf.4
    cbvralcsf.6
    sbie
    syl6bb
    anbi12d
    cbveu
    bitri
    wph
    vx
    cA
    df-reu
    wps
    vy
    cB
    df-reu
    3bitr4i
end
