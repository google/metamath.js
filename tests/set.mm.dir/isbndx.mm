include "cbnd.mm"
include "cfv.mm"
include "wcel.mm"
include "cme.mm"
include "cv.mm"
include "cbl.mm"
include "co.mm"
include "wceq.mm"
include "crp.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "cxmt.mm"
include "isbnd.mm"
include "metxmet.mm"
include "cxp.mm"
include "cr.mm"
include "wf.mm"
include "simpr.mm"
include "wfn.mm"
include "cxr.mm"
include "xmetf.mm"
include "ffn.mm"
include "3syl.mm"
include "ccnv.mm"
include "cima.mm"
include "wbr.mm"
include "w3a.mm"
include "cec.mm"
include "simprr.mm"
include "wss.mm"
include "rpxr.mm"
include "eqid.mm"
include "blssec.mm"
include "3expa.mm"
include "sylan2.mm"
include "adantrr.mm"
include "eqsstrd.mm"
include "sselda.mm"
include "vex.mm"
include "elec.mm"
include "sylib.mm"
include "wb.mm"
include "xmeterval.mm"
include "ad3antrrr.mm"
include "mpbid.mm"
include "simp3d.mm"
include "ralrimiva.mm"
include "rexlimdvaa.mm"
include "ralimdva.mm"
include "impcom.mm"
include "ffnov.mm"
include "sylanbrc.mm"
include "ismet2.mm"
include "ex.mm"
include "impbid2.mm"
include "pm5.32ri.mm"
include "bitri.mm"

theorem isbndx
  let vx: setvar x
  let cM: class M
  let cX: class X
  let vr: setvar r
  let vd: setvar d
  let vm: setvar m
  let vs: setvar s
  let vy: setvar y
  let vz: setvar z
  let cN: class N
  let cP: class P
  let cR: class R
  let cS: class S
  let cY: class Y

  disjoint r x
  disjoint M r
  disjoint M x
  disjoint X r
  disjoint X x
  disjoint d m
  disjoint d r
  disjoint d s
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint M d
  disjoint m r
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint M m
  disjoint r s
  disjoint r y
  disjoint r z
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint M s
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint M y
  disjoint M z
  disjoint N d
  disjoint N r
  disjoint N y
  disjoint P d
  disjoint P r
  disjoint P y
  disjoint X d
  disjoint X m
  disjoint X s
  disjoint X y
  disjoint X z
  disjoint R r
  disjoint R x
  disjoint S r
  disjoint S x
  disjoint Y d
  disjoint Y r
  disjoint Y x
  disjoint Y y
  assert |- ( M e. ( Bnd ` X ) <-> ( M e. ( *Met ` X ) /\ A. x e. X E. r e. RR+ X = ( x ( ball ` M ) r ) ) )

  proof
    cM
    cX
    cbnd
    cfv
    wcel
    cM
    cX
    cme
    cfv
    wcel
    #
    cX
    vx
    cv
    #
    vr
    cv
    #
    cM
    cbl
    cfv
    co
    #
    wceq
    #
    vr
    crp
    wrex
    #
    vx
    cX
    wral
    #
    wa
    cM
    cX
    cxmt
    cfv
    wcel
    #
    @6
    wa
    vx
    cM
    cX
    vr
    isbnd
    @6
    @0
    @7
    @6
    @0
    @7
    cM
    cX
    metxmet
    @6
    @7
    @0
    @6
    @7
    wa
    #
    @7
    cX
    cX
    cxp
    #
    cr
    cM
    wf
    #
    @0
    @6
    @7
    simpr
    #
    @8
    cM
    @9
    wfn
    #
    @1
    vy
    cv
    #
    cM
    co
    cr
    wcel
    #
    vy
    cX
    wral
    #
    vx
    cX
    wral
    #
    @10
    @8
    @7
    @9
    cxr
    cM
    wf
    @12
    @11
    cM
    cX
    xmetf
    @9
    cxr
    cM
    ffn
    3syl
    @7
    @6
    @16
    @7
    @5
    @15
    vx
    cX
    @7
    @1
    cX
    wcel
    #
    wa
    #
    @4
    @15
    vr
    crp
    @18
    @2
    crp
    wcel
    #
    @4
    wa
    #
    wa
    #
    @14
    vy
    cX
    @21
    @13
    cX
    wcel
    #
    wa
    #
    @17
    @22
    @14
    @23
    @1
    @13
    cM
    ccnv
    cr
    cima
    #
    wbr
    #
    @17
    @22
    @14
    w3a
    #
    @23
    @13
    @1
    @24
    cec
    #
    wcel
    @25
    @21
    cX
    @27
    @13
    @21
    cX
    @3
    @27
    @18
    @19
    @4
    simprr
    @18
    @19
    @3
    @27
    wss
    #
    @4
    @19
    @18
    @2
    cxr
    wcel
    #
    @28
    @2
    rpxr
    @7
    @17
    @29
    @28
    cM
    @1
    @24
    @2
    cX
    @24
    eqid
    #
    blssec
    3expa
    sylan2
    adantrr
    eqsstrd
    sselda
    @13
    @1
    @24
    vy
    vex
    vx
    vex
    elec
    sylib
    @7
    @25
    @26
    wb
    @17
    @20
    @22
    @1
    @13
    cM
    @24
    cX
    @30
    xmeterval
    ad3antrrr
    mpbid
    simp3d
    ralrimiva
    rexlimdvaa
    ralimdva
    impcom
    vx
    vy
    cX
    cX
    cr
    cM
    ffnov
    sylanbrc
    cM
    cX
    ismet2
    sylanbrc
    ex
    impbid2
    pm5.32ri
    bitri
end
