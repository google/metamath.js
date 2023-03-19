include "cbnd.mm"
include "cfv.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cxmt.mm"
include "cv.mm"
include "cbl.mm"
include "co.mm"
include "wceq.mm"
include "crp.mm"
include "wrex.mm"
include "wral.mm"
include "isbndx.mm"
include "anbi1i.mm"
include "anass.mm"
include "r19.2z.mm"
include "ancoms.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "oveq2.mm"
include "cbvrex2v.mm"
include "c2.mm"
include "cmul.mm"
include "2rp.mm"
include "rpmulcl.mm"
include "mpan.mm"
include "ad2antll.mm"
include "ad2antrr.mm"
include "cdiv.mm"
include "wss.mm"
include "wi.mm"
include "cc.mm"
include "cc0.mm"
include "rpcn.mm"
include "2cnd.mm"
include "2ne0.mm"
include "a1i.mm"
include "w3a.mm"
include "divcan3.mm"
include "eqcomd.mm"
include "syl3anc.mm"
include "oveq2d.mm"
include "biimpd.mm"
include "adantr.mm"
include "imp.mm"
include "simpr.mm"
include "eleq2.mm"
include "biimpac.mm"
include "cr.mm"
include "2re.mm"
include "rpre.mm"
include "remulcl.mm"
include "sylancr.mm"
include "blhalf.mm"
include "expr.mm"
include "sylan2.mm"
include "anasss.mm"
include "anassrs.mm"
include "eqsstrd.mm"
include "syldan.mm"
include "adantl.mm"
include "cxr.mm"
include "rpxr.mm"
include "blssm.mm"
include "syl3an3.mm"
include "3expa.mm"
include "an32s.mm"
include "eqssd.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ex.mm"
include "ralrimdva.mm"
include "rexlimdvva.mm"
include "syl5bi.mm"
include "rexn0.mm"
include "jcad.mm"
include "impbid2.mm"
include "pm5.32i.mm"
include "3bitri.mm"

theorem isbnd2
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
  assert |- ( ( M e. ( Bnd ` X ) /\ X =/= (/) ) <-> ( M e. ( *Met ` X ) /\ E. x e. X E. r e. RR+ X = ( x ( ball ` M ) r ) ) )

  proof
    cM
    cX
    cbnd
    cfv
    wcel
    #
    cX
    c0
    wne
    #
    wa
    cM
    cX
    cxmt
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
    #
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
    #
    @1
    wa
    @2
    @9
    @1
    wa
    #
    wa
    @2
    @8
    vx
    cX
    wrex
    #
    wa
    @0
    @10
    @1
    vx
    cM
    cX
    vr
    isbndx
    anbi1i
    @2
    @9
    @1
    anass
    @2
    @11
    @12
    @2
    @11
    @12
    @1
    @9
    @12
    @8
    vx
    cX
    r19.2z
    ancoms
    @2
    @12
    @9
    @1
    @12
    cX
    vy
    cv
    #
    vs
    cv
    #
    @5
    co
    #
    wceq
    #
    vs
    crp
    wrex
    vy
    cX
    wrex
    @2
    @9
    @7
    @16
    cX
    @13
    @4
    @5
    co
    #
    wceq
    vx
    vr
    vy
    vs
    cX
    crp
    @3
    @13
    wceq
    @6
    @17
    cX
    @3
    @13
    @4
    @5
    oveq1
    eqeq2d
    @4
    @14
    wceq
    @17
    @15
    cX
    @4
    @14
    @13
    @5
    oveq2
    eqeq2d
    cbvrex2v
    @2
    @16
    @9
    vy
    vs
    cX
    crp
    @2
    @13
    cX
    wcel
    #
    @14
    crp
    wcel
    #
    wa
    #
    wa
    #
    @16
    @8
    vx
    cX
    @21
    @3
    cX
    wcel
    #
    wa
    #
    @16
    @8
    @23
    @16
    wa
    #
    c2
    @14
    cmul
    co
    #
    crp
    wcel
    #
    cX
    @3
    @25
    @5
    co
    #
    wceq
    #
    @8
    @21
    @26
    @22
    @16
    @19
    @26
    @2
    @18
    c2
    crp
    wcel
    @19
    @26
    2rp
    c2
    @14
    rpmulcl
    mpan
    #
    ad2antll
    ad2antrr
    @24
    cX
    @27
    @23
    @16
    cX
    @13
    @25
    c2
    cdiv
    co
    #
    @5
    co
    #
    wceq
    #
    cX
    @27
    wss
    @23
    @16
    @32
    @21
    @16
    @32
    wi
    #
    @22
    @19
    @33
    @2
    @18
    @19
    @16
    @32
    @19
    @15
    @31
    cX
    @19
    @14
    @30
    @13
    @5
    @19
    @14
    cc
    wcel
    #
    c2
    cc
    wcel
    #
    c2
    cc0
    wne
    #
    @14
    @30
    wceq
    @14
    rpcn
    @19
    2cnd
    @36
    @19
    2ne0
    a1i
    @34
    @35
    @36
    w3a
    @30
    @14
    @14
    c2
    divcan3
    eqcomd
    syl3anc
    oveq2d
    eqeq2d
    biimpd
    ad2antll
    adantr
    imp
    @23
    @32
    wa
    cX
    @31
    @27
    @23
    @32
    simpr
    @21
    @22
    @32
    @31
    @27
    wss
    #
    @22
    @32
    wa
    @21
    @3
    @31
    wcel
    #
    @37
    @32
    @22
    @38
    cX
    @31
    @3
    eleq2
    biimpac
    @21
    @38
    @37
    @2
    @18
    @19
    @38
    @37
    wi
    #
    @19
    @2
    @18
    wa
    #
    @25
    cr
    wcel
    #
    @39
    @19
    c2
    cr
    wcel
    @14
    cr
    wcel
    @41
    2re
    @14
    rpre
    c2
    @14
    remulcl
    sylancr
    @40
    @41
    @38
    @37
    @25
    cM
    cX
    @13
    @3
    blhalf
    expr
    sylan2
    anasss
    imp
    sylan2
    anassrs
    eqsstrd
    syldan
    @23
    @27
    cX
    wss
    #
    @16
    @2
    @22
    @20
    @42
    @20
    @2
    @22
    wa
    @26
    @42
    @19
    @26
    @18
    @29
    adantl
    @2
    @22
    @26
    @42
    @26
    @2
    @22
    @25
    cxr
    wcel
    @42
    @25
    rpxr
    cM
    @3
    @25
    cX
    blssm
    syl3an3
    3expa
    sylan2
    an32s
    adantr
    eqssd
    @7
    @28
    vr
    @25
    crp
    @4
    @25
    wceq
    @6
    @27
    cX
    @4
    @25
    @3
    @5
    oveq2
    eqeq2d
    rspcev
    syl2anc
    ex
    ralrimdva
    rexlimdvva
    syl5bi
    @12
    @1
    wi
    @2
    @8
    vx
    cX
    rexn0
    a1i
    jcad
    impbid2
    pm5.32i
    3bitri
end
