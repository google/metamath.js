include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cnei.mm"
include "cuni.mm"
include "wss.mm"
include "cv.mm"
include "wrex.mm"
include "cbl.mm"
include "co.mm"
include "crp.mm"
include "ctop.mm"
include "wb.mm"
include "mopntop.mm"
include "adantr.mm"
include "mopnuni.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "eqid.mm"
include "isneip.mm"
include "syl2anc.mm"
include "sseq2d.mm"
include "anbi1d.mm"
include "wi.mm"
include "w3a.mm"
include "mopni2.mm"
include "sstr2.mm"
include "com12.mm"
include "reximdv.mm"
include "syl5com.mm"
include "3exp.mm"
include "imp4a.mm"
include "ad2antrr.mm"
include "rexlimdv.mm"
include "cxr.mm"
include "rpxr.mm"
include "blopn.mm"
include "syl3an3.mm"
include "blcntr.mm"
include "wceq.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "expr.mm"
include "3expia.mm"
include "impbid.mm"
include "pm5.32da.mm"
include "3bitr2d.mm"

theorem neibl
  let cD: class D
  let cP: class P
  let cJ: class J
  let cN: class N
  let cX: class X
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vw: setvar w
  let vz: setvar z
  let cR: class R
  let cS: class S
  let cT: class T
  assume mopni.1: |- J = ( MetOpen ` D )

  disjoint D r
  disjoint J r
  disjoint N r
  disjoint P r
  disjoint X r
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint D w
  disjoint x z
  disjoint D x
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint J x
  disjoint J y
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint N y
  disjoint P w
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint T z
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ( D e. ( *Met ` X ) /\ P e. X ) -> ( N e. ( ( nei ` J ) ` { P } ) <-> ( N C_ X /\ E. r e. RR+ ( P ( ball ` D ) r ) C_ N ) ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cP
    cX
    wcel
    #
    wa
    #
    cN
    cP
    csn
    cJ
    cnei
    cfv
    cfv
    wcel
    #
    cN
    cJ
    cuni
    #
    wss
    #
    cP
    vy
    cv
    #
    wcel
    #
    @6
    cN
    wss
    #
    wa
    #
    vy
    cJ
    wrex
    #
    wa
    #
    cN
    cX
    wss
    #
    @10
    wa
    @12
    cP
    vr
    cv
    #
    cD
    cbl
    cfv
    co
    #
    cN
    wss
    #
    vr
    crp
    wrex
    #
    wa
    @2
    cJ
    ctop
    wcel
    #
    cP
    @4
    wcel
    #
    @3
    @11
    wb
    @0
    @17
    @1
    cD
    cJ
    cX
    mopni.1
    mopntop
    adantr
    @0
    @1
    @18
    @0
    cX
    @4
    cP
    cD
    cJ
    cX
    mopni.1
    mopnuni
    #
    eleq2d
    biimpa
    cP
    vy
    cJ
    cN
    @4
    @4
    eqid
    isneip
    syl2anc
    @2
    @12
    @5
    @10
    @0
    @12
    @5
    wb
    @1
    @0
    cX
    @4
    cN
    @19
    sseq2d
    adantr
    anbi1d
    @2
    @12
    @10
    @16
    @2
    @12
    wa
    #
    @10
    @16
    @20
    @9
    @16
    vy
    cJ
    @0
    @6
    cJ
    wcel
    #
    @9
    @16
    wi
    wi
    @1
    @12
    @0
    @21
    @7
    @8
    @16
    @0
    @21
    @7
    @8
    @16
    wi
    @0
    @21
    @7
    w3a
    @14
    @6
    wss
    #
    vr
    crp
    wrex
    @8
    @16
    vr
    @6
    cD
    cP
    cJ
    cX
    mopni.1
    mopni2
    @8
    @22
    @15
    vr
    crp
    @22
    @8
    @15
    @14
    @6
    cN
    sstr2
    com12
    reximdv
    syl5com
    3exp
    imp4a
    ad2antrr
    rexlimdv
    @2
    @16
    @10
    wi
    @12
    @2
    @15
    @10
    vr
    crp
    @0
    @1
    @13
    crp
    wcel
    #
    @15
    @10
    wi
    #
    @0
    @1
    @23
    w3a
    @14
    cJ
    wcel
    #
    cP
    @14
    wcel
    #
    @24
    @23
    @0
    @1
    @13
    cxr
    wcel
    @25
    @13
    rpxr
    cD
    cP
    @13
    cJ
    cX
    mopni.1
    blopn
    syl3an3
    cD
    cP
    @13
    cX
    blcntr
    @25
    @26
    @15
    @10
    @9
    @26
    @15
    wa
    vy
    @14
    cJ
    @6
    @14
    wceq
    @7
    @26
    @8
    @15
    @6
    @14
    cP
    eleq2
    @6
    @14
    cN
    sseq1
    anbi12d
    rspcev
    expr
    syl2anc
    3expia
    rexlimdv
    adantr
    impbid
    pm5.32da
    3bitr2d
end
