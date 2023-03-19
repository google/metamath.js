include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "clp.mm"
include "cfv.mm"
include "cpw.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "ccl.mm"
include "cab.mm"
include "cmpt.mm"
include "wceq.mm"
include "lpfval.mm"
include "fveq1d.mm"
include "adantr.mm"
include "cvv.mm"
include "wb.mm"
include "topopn.mm"
include "elpw2g.mm"
include "syl.mm"
include "biimpar.mm"
include "wi.mm"
include "ssdifss.mm"
include "clsss3.mm"
include "sseld.mm"
include "sylan2.mm"
include "abssdv.mm"
include "ssexd.mm"
include "difeq1.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "abbidv.mm"
include "eqid.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem lpval
  let vx: setvar x
  let cS: class S
  let cJ: class J
  let cX: class X
  let vj: setvar j
  let vn: setvar n
  let vy: setvar y
  let cP: class P
  let cT: class T
  assume lpfval.1: |- X = U. J

  disjoint J x
  disjoint S x
  disjoint X x
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint J j
  disjoint n x
  disjoint n y
  disjoint J n
  disjoint x y
  disjoint J y
  disjoint P n
  disjoint P x
  disjoint P y
  disjoint S n
  disjoint S y
  disjoint T x
  disjoint X j
  disjoint X n
  disjoint X y
  assert |- ( ( J e. Top /\ S C_ X ) -> ( ( limPt ` J ) ` S ) = { x | x e. ( ( cls ` J ) ` ( S \ { x } ) ) } )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cX
    wss
    #
    wa
    #
    cS
    cJ
    clp
    cfv
    #
    cfv
    #
    cS
    vy
    cX
    cpw
    #
    vx
    cv
    #
    vy
    cv
    #
    @6
    csn
    #
    cdif
    #
    cJ
    ccl
    cfv
    #
    cfv
    #
    wcel
    #
    vx
    cab
    #
    cmpt
    #
    cfv
    #
    @6
    cS
    @8
    cdif
    #
    @10
    cfv
    #
    wcel
    #
    vx
    cab
    #
    @0
    @4
    @15
    wceq
    @1
    @0
    cS
    @3
    @14
    vy
    vx
    cJ
    cX
    lpfval.1
    lpfval
    fveq1d
    adantr
    @2
    cS
    @5
    wcel
    #
    @19
    cvv
    wcel
    @15
    @19
    wceq
    @0
    @20
    @1
    @0
    cX
    cJ
    wcel
    #
    @20
    @1
    wb
    cJ
    cX
    lpfval.1
    topopn
    #
    cS
    cX
    cJ
    elpw2g
    syl
    biimpar
    @2
    @19
    cX
    cJ
    @0
    @21
    @1
    @22
    adantr
    @2
    @18
    vx
    cX
    @1
    @0
    @16
    cX
    wss
    #
    @18
    @6
    cX
    wcel
    wi
    cS
    cX
    @8
    ssdifss
    @0
    @23
    wa
    @17
    cX
    @6
    @16
    cJ
    cX
    lpfval.1
    clsss3
    sseld
    sylan2
    abssdv
    ssexd
    vy
    cS
    @13
    @19
    @5
    cvv
    @14
    @7
    cS
    wceq
    #
    @12
    @18
    vx
    @24
    @11
    @17
    @6
    @24
    @9
    @16
    @10
    @7
    cS
    @8
    difeq1
    fveq2d
    eleq2d
    abbidv
    @14
    eqid
    fvmptg
    syl2anc
    eqtrd
end
