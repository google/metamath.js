include "cxp.mm"
include "wral.mm"
include "wsb.mm"
include "cbvralsv.mm"
include "ralbii.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfs1v.mm"
include "nfral.mm"
include "cv.mm"
include "wceq.mm"
include "sbequ12.mm"
include "ralbidv.mm"
include "cbvral.mm"
include "cop.mm"
include "wa.mm"
include "wex.mm"
include "wb.mm"
include "vex.mm"
include "eqvinop.mm"
include "nfsb.mm"
include "nfbi.mm"
include "sbhypf.mm"
include "opth.mm"
include "sylan9bb.mm"
include "sylbi.mm"
include "exlimi.mm"
include "ralxp.mm"
include "3bitr4ri.mm"
include "bitri.mm"

theorem ralxpf
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume ralxpf.1: |- F/ y ph
  assume ralxpf.2: |- F/ z ph
  assume ralxpf.3: |- F/ x ps
  assume ralxpf.4: |- ( x = <. y , z >. -> ( ph <-> ps ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint u z
  disjoint B u
  disjoint v z
  disjoint B v
  disjoint w z
  disjoint B w
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ps u
  disjoint ps v
  disjoint ps w
  assert |- ( A. x e. ( A X. B ) ph <-> A. y e. A A. z e. B ps )

  proof
    wph
    vx
    cA
    cB
    cxp
    #
    wral
    wph
    vx
    vw
    wsb
    #
    vw
    @0
    wral
    #
    wps
    vz
    cB
    wral
    #
    vy
    cA
    wral
    #
    wph
    vx
    vw
    @0
    cbvralsv
    wps
    vy
    vu
    wsb
    #
    vz
    cB
    wral
    #
    vu
    cA
    wral
    @5
    vz
    vv
    wsb
    #
    vv
    cB
    wral
    #
    vu
    cA
    wral
    @4
    @2
    @6
    @8
    vu
    cA
    @5
    vz
    vv
    cB
    cbvralsv
    ralbii
    @3
    @6
    vy
    vu
    cA
    @3
    vu
    nfv
    @5
    vy
    vz
    cB
    vy
    cB
    nfcv
    wps
    vy
    vu
    nfs1v
    #
    nfral
    vy
    cv
    #
    vu
    cv
    #
    wceq
    #
    wps
    @5
    vz
    cB
    wps
    vy
    vu
    sbequ12
    #
    ralbidv
    cbvral
    @1
    @7
    vw
    vu
    vv
    cA
    cB
    vw
    cv
    #
    @11
    vv
    cv
    #
    cop
    #
    wceq
    @14
    @10
    vz
    cv
    #
    cop
    #
    wceq
    #
    @18
    @16
    wceq
    #
    wa
    #
    vz
    wex
    #
    vy
    wex
    @1
    @7
    wb
    #
    vy
    vz
    @14
    @11
    @15
    vu
    vex
    vv
    vex
    eqvinop
    @22
    @23
    vy
    @1
    @7
    vy
    wph
    vx
    vw
    vy
    ralxpf.1
    nfsb
    @5
    vz
    vv
    vy
    @9
    nfsb
    nfbi
    @21
    @23
    vz
    @1
    @7
    vz
    wph
    vx
    vw
    vz
    ralxpf.2
    nfsb
    @5
    vz
    vv
    nfs1v
    nfbi
    @19
    @1
    wps
    @20
    @7
    wph
    wps
    vx
    vw
    @18
    ralxpf.3
    ralxpf.4
    sbhypf
    @20
    @12
    @17
    @15
    wceq
    #
    wa
    wps
    @7
    wb
    @10
    @17
    @11
    @15
    vy
    vex
    vz
    vex
    opth
    @12
    wps
    @5
    @24
    @7
    @13
    @5
    vz
    vv
    sbequ12
    sylan9bb
    sylbi
    sylan9bb
    exlimi
    exlimi
    sylbi
    ralxp
    3bitr4ri
    bitri
end
