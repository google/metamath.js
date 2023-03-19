include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "ccl.mm"
include "cfv.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "wral.mm"
include "csn.mm"
include "cnei.mm"
include "elcls.mm"
include "wa.mm"
include "wrex.mm"
include "isneip.mm"
include "r19.29r.mm"
include "pm3.35.mm"
include "wceq.mm"
include "ssrin.mm"
include "sseq2.mm"
include "ss0.mm"
include "syl6bi.mm"
include "syl5com.mm"
include "necon3d.mm"
include "ex.mm"
include "com23.mm"
include "imp31.mm"
include "rexlimivw.mm"
include "syl.mm"
include "adantl.mm"
include "3adant2.mm"
include "imp.mm"
include "ralrimiv.mm"
include "opnneip.mm"
include "weq.mm"
include "ineq1.mm"
include "neeq1d.mm"
include "rspccva.mm"
include "idd.mm"
include "3exp.mm"
include "com14.mm"
include "com3l.mm"
include "mpcom.mm"
include "3expia.mm"
include "com25.mm"
include "3imp1.mm"
include "impbida.mm"
include "bitrd.mm"

theorem neindisj2
  let cP: class P
  let cS: class S
  let vn: setvar n
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let cK: class K
  let cY: class Y
  assume tpnei.1: |- X = U. J

  disjoint J n
  disjoint P n
  disjoint S n
  disjoint X n
  disjoint J x
  disjoint n x
  disjoint K x
  disjoint P x
  disjoint S x
  disjoint X x
  disjoint Y x
  assert |- ( ( J e. Top /\ S C_ X /\ P e. X ) -> ( P e. ( ( cls ` J ) ` S ) <-> A. n e. ( ( nei ` J ) ` { P } ) ( n i^i S ) =/= (/) ) )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cX
    wss
    #
    cP
    cX
    wcel
    #
    w3a
    #
    cP
    cS
    cJ
    ccl
    cfv
    cfv
    wcel
    cP
    vx
    cv
    #
    wcel
    #
    @4
    cS
    cin
    #
    c0
    wne
    #
    wi
    #
    vx
    cJ
    wral
    #
    vn
    cv
    #
    cS
    cin
    #
    c0
    wne
    #
    vn
    cP
    csn
    cJ
    cnei
    cfv
    cfv
    #
    wral
    #
    vx
    cP
    cS
    cJ
    cX
    tpnei.1
    elcls
    @3
    @9
    @14
    @3
    @9
    wa
    @12
    vn
    @13
    @3
    @9
    @10
    @13
    wcel
    #
    @12
    wi
    @3
    @15
    @9
    @12
    @0
    @2
    @15
    @9
    @12
    wi
    #
    wi
    @1
    @0
    @2
    wa
    @15
    @10
    cX
    wss
    #
    @5
    @4
    @10
    wss
    #
    wa
    #
    vx
    cJ
    wrex
    #
    wa
    @16
    cP
    vx
    cJ
    @10
    cX
    tpnei.1
    isneip
    @20
    @16
    @17
    @20
    @9
    @12
    @20
    @9
    wa
    @19
    @8
    wa
    #
    vx
    cJ
    wrex
    @12
    @19
    @8
    vx
    cJ
    r19.29r
    @21
    @12
    vx
    cJ
    @5
    @18
    @8
    @12
    @5
    @8
    @18
    @12
    @5
    @8
    @18
    @12
    wi
    @5
    @8
    wa
    @7
    @18
    @12
    @5
    @7
    pm3.35
    @18
    @11
    c0
    @6
    c0
    @18
    @6
    @11
    wss
    #
    @11
    c0
    wceq
    #
    @6
    c0
    wceq
    #
    @4
    @10
    cS
    ssrin
    @23
    @22
    @6
    c0
    wss
    @24
    @11
    c0
    @6
    sseq2
    @6
    ss0
    syl6bi
    syl5com
    necon3d
    syl5com
    ex
    com23
    imp31
    rexlimivw
    syl
    ex
    adantl
    syl6bi
    3adant2
    com23
    imp
    ralrimiv
    @3
    @14
    wa
    @8
    vx
    cJ
    @0
    @1
    @2
    @14
    @4
    cJ
    wcel
    #
    @8
    wi
    @0
    @25
    @2
    @14
    @1
    @8
    @0
    @25
    @2
    @14
    @1
    @8
    wi
    wi
    wi
    @0
    @25
    wa
    @5
    @14
    @1
    @2
    @7
    @0
    @25
    @5
    @14
    @1
    @2
    @7
    wi
    wi
    #
    wi
    #
    @4
    @13
    wcel
    #
    @0
    @25
    @5
    w3a
    #
    @27
    cP
    cJ
    @4
    opnneip
    @14
    @28
    @29
    @26
    @14
    @28
    @29
    @26
    wi
    #
    @14
    @28
    wa
    @7
    @30
    @12
    @7
    vn
    @4
    @13
    vn
    vx
    weq
    @11
    @6
    c0
    @10
    @4
    cS
    ineq1
    neeq1d
    rspccva
    @2
    @29
    @1
    @7
    @7
    @2
    @29
    @1
    @7
    @7
    wi
    @2
    @29
    @1
    w3a
    @7
    idd
    3exp
    com14
    syl
    ex
    com3l
    mpcom
    3expia
    com25
    ex
    com25
    3imp1
    ralrimiv
    impbida
    bitrd
end
