include "cv.mm"
include "cxp.mm"
include "wcel.mm"
include "wa.mm"
include "copab.mm"
include "wsb.mm"
include "coprab.mm"
include "cop.mm"
include "wceq.mm"
include "wb.mm"
include "wi.mm"
include "nfv.mm"
include "nfs1v.mm"
include "nfbi.mm"
include "nfim.mm"
include "opeq1.mm"
include "eqeq2d.mm"
include "sbequ12.mm"
include "bibi2d.mm"
include "imbi12d.mm"
include "opeq2.mm"
include "chvar.mm"
include "dfoprab4.mm"
include "nfan.mm"
include "nfsb.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "sylan9bbr.mm"
include "anbi12d.mm"
include "cbvoprab12.mm"
include "eqtr4i.mm"

theorem dfoprab4f
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let vt: setvar t
  let vu: setvar u
  assume dfoprab4f.x: |- F/ x ph
  assume dfoprab4f.y: |- F/ y ph
  assume dfoprab4f.1: |- ( w = <. x , y >. -> ( ph <-> ps ) )

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint ps w
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A t
  disjoint A u
  disjoint B t
  disjoint B u
  disjoint ps t
  disjoint ps u
  disjoint ph t
  disjoint ph u
  assert |- { <. w , z >. | ( w e. ( A X. B ) /\ ph ) } = { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ ps ) }

  proof
    vw
    cv
    #
    cA
    cB
    cxp
    wcel
    wph
    wa
    vw
    vz
    copab
    vt
    cv
    #
    cA
    wcel
    #
    vu
    cv
    #
    cB
    wcel
    #
    wa
    #
    wps
    vy
    vu
    wsb
    #
    vx
    vt
    wsb
    #
    wa
    #
    vt
    vu
    vz
    coprab
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    #
    wps
    wa
    #
    vx
    vy
    vz
    coprab
    wph
    @7
    vt
    vu
    vz
    vw
    cA
    cB
    @0
    @9
    @3
    cop
    #
    wceq
    #
    wph
    @6
    wb
    #
    wi
    #
    @0
    @1
    @3
    cop
    #
    wceq
    #
    wph
    @7
    wb
    #
    wi
    vx
    vt
    @20
    @21
    vx
    @20
    vx
    nfv
    wph
    @7
    vx
    dfoprab4f.x
    @6
    vx
    vt
    nfs1v
    #
    nfbi
    nfim
    @9
    @1
    wceq
    #
    @16
    @20
    @17
    @21
    @23
    @15
    @19
    @0
    @9
    @1
    @3
    opeq1
    eqeq2d
    @23
    @6
    @7
    wph
    @6
    vx
    vt
    sbequ12
    #
    bibi2d
    imbi12d
    @0
    @9
    @11
    cop
    #
    wceq
    #
    wph
    wps
    wb
    #
    wi
    @18
    vy
    vu
    @16
    @17
    vy
    @16
    vy
    nfv
    wph
    @6
    vy
    dfoprab4f.y
    wps
    vy
    vu
    nfs1v
    #
    nfbi
    nfim
    @11
    @3
    wceq
    #
    @26
    @16
    @27
    @17
    @29
    @25
    @15
    @0
    @11
    @3
    @9
    opeq2
    eqeq2d
    @29
    wps
    @6
    wph
    wps
    vy
    vu
    sbequ12
    #
    bibi2d
    imbi12d
    dfoprab4f.1
    chvar
    chvar
    dfoprab4
    @14
    @8
    vx
    vy
    vz
    vt
    vu
    @14
    vt
    nfv
    @14
    vu
    nfv
    @5
    @7
    vx
    @5
    vx
    nfv
    @22
    nfan
    @5
    @7
    vy
    @5
    vy
    nfv
    @6
    vx
    vt
    vy
    @28
    nfsb
    nfan
    @23
    @29
    wa
    @13
    @5
    wps
    @7
    @23
    @10
    @2
    @29
    @12
    @4
    @9
    @1
    cA
    eleq1
    @11
    @3
    cB
    eleq1
    bi2anan9
    @29
    wps
    @6
    @23
    @7
    @30
    @24
    sylan9bbr
    anbi12d
    cbvoprab12
    eqtr4i
end
