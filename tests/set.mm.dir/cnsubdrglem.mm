include "ccnfld.mm"
include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "cress.mm"
include "co.mm"
include "cdr.mm"
include "cnsubrglem.mm"
include "cv.mm"
include "cinvr.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "wb.mm"
include "cndrng.mm"
include "eqid.mm"
include "cnfld0.mm"
include "issubdrg.mm"
include "mp2an.mm"
include "c1.mm"
include "cdiv.mm"
include "crg.mm"
include "cc.mm"
include "wceq.mm"
include "cnring.mm"
include "wss.mm"
include "ssriv.mm"
include "ssdif.mm"
include "ax-mp.mm"
include "sseli.mm"
include "cnfldbas.mm"
include "drngui.mm"
include "cnflddiv.mm"
include "cnfld1.mm"
include "ringinvdv.mm"
include "sylancr.mm"
include "wne.mm"
include "wa.mm"
include "eldifsn.mm"
include "sylbi.mm"
include "eqeltrd.mm"
include "mprgbir.mm"
include "pm3.2i.mm"

theorem cnsubdrglem
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume cnsubglem.1: |- ( x e. A -> x e. CC )
  assume cnsubglem.2: |- ( ( x e. A /\ y e. A ) -> ( x + y ) e. A )
  assume cnsubglem.3: |- ( x e. A -> -u x e. A )
  assume cnsubrglem.4: |- 1 e. A
  assume cnsubrglem.5: |- ( ( x e. A /\ y e. A ) -> ( x x. y ) e. A )
  assume cnsubrglem.6: |- ( ( x e. A /\ x =/= 0 ) -> ( 1 / x ) e. A )

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( A e. ( SubRing ` CCfld ) /\ ( CCfld |`s A ) e. DivRing )

  proof
    cA
    ccnfld
    csubrg
    cfv
    wcel
    #
    ccnfld
    cA
    cress
    co
    #
    cdr
    wcel
    #
    vx
    vy
    cA
    cnsubglem.1
    cnsubglem.2
    cnsubglem.3
    cnsubrglem.4
    cnsubrglem.5
    cnsubrglem
    #
    @2
    vx
    cv
    #
    ccnfld
    cinvr
    cfv
    #
    cfv
    #
    cA
    wcel
    #
    vx
    cA
    cc0
    csn
    #
    cdif
    #
    ccnfld
    cdr
    wcel
    @0
    @2
    @7
    vx
    @9
    wral
    wb
    cndrng
    @3
    vx
    cA
    ccnfld
    @1
    @5
    cc0
    @1
    eqid
    cnfld0
    @5
    eqid
    #
    issubdrg
    mp2an
    @4
    @9
    wcel
    #
    @6
    c1
    @4
    cdiv
    co
    #
    cA
    @11
    ccnfld
    crg
    wcel
    @4
    cc
    @8
    cdif
    #
    wcel
    @6
    @12
    wceq
    cnring
    @9
    @13
    @4
    cA
    cc
    wss
    @9
    @13
    wss
    vx
    cA
    cc
    cnsubglem.1
    ssriv
    cA
    cc
    @8
    ssdif
    ax-mp
    sseli
    cc
    cdiv
    ccnfld
    @13
    c1
    @5
    @4
    cnfldbas
    cc
    ccnfld
    cc0
    cnfldbas
    cnfld0
    cndrng
    drngui
    cnflddiv
    cnfld1
    @10
    ringinvdv
    sylancr
    @11
    @4
    cA
    wcel
    @4
    cc0
    wne
    wa
    @12
    cA
    wcel
    @4
    cA
    cc0
    eldifsn
    cnsubrglem.6
    sylbi
    eqeltrd
    mprgbir
    pm3.2i
end
