include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cbl.mm"
include "crn.mm"
include "ctg.mm"
include "cv.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "cuni.mm"
include "co.mm"
include "crp.mm"
include "wceq.mm"
include "mopnval.mm"
include "adantr.mm"
include "adantl.mm"
include "sseq12d.mm"
include "ctb.mm"
include "wb.mm"
include "blbas.mm"
include "unirnbl.mm"
include "eqtr4d.mm"
include "tgss2.mm"
include "syl2anc.mm"
include "raleqdv.mm"
include "blssex.mm"
include "adantll.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "w3a.mm"
include "cxr.mm"
include "rpxr.mm"
include "blelrn.mm"
include "syl3an3.mm"
include "blcntr.mm"
include "eleq2.mm"
include "sseq2.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "com23.mm"
include "sylc.mm"
include "3expa.mm"
include "adantllr.mm"
include "ralrimdva.mm"
include "blss.mm"
include "3expb.mm"
include "adantlr.mm"
include "r19.29.mm"
include "sstr.mm"
include "expcom.mm"
include "reximdv.mm"
include "impcom.mm"
include "rexlimivw.mm"
include "syl.mm"
include "ex.mm"
include "syl5com.mm"
include "expr.mm"
include "impbid.mm"
include "bitrd.mm"
include "ralbidva.mm"
include "3bitrd.mm"

theorem metss
  let vx: setvar x
  let cC: class C
  let cD: class D
  let cJ: class J
  let cK: class K
  let cX: class X
  let vs: setvar s
  let vr: setvar r
  let vy: setvar y
  let vz: setvar z
  let cR: class R
  let cS: class S
  let wph: wff ph
  let va: setvar a
  let vb: setvar b
  assume metequiv.3: |- J = ( MetOpen ` C )
  assume metequiv.4: |- K = ( MetOpen ` D )

  disjoint r s
  disjoint r x
  disjoint C r
  disjoint s x
  disjoint C s
  disjoint C x
  disjoint J r
  disjoint J s
  disjoint J x
  disjoint K r
  disjoint K s
  disjoint K x
  disjoint D r
  disjoint D s
  disjoint D x
  disjoint X r
  disjoint X s
  disjoint X x
  disjoint r y
  disjoint r z
  disjoint s y
  disjoint s z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint J y
  disjoint K y
  disjoint R s
  disjoint R y
  disjoint S y
  disjoint D y
  disjoint D z
  disjoint ph r
  disjoint ph x
  disjoint ph y
  disjoint X y
  disjoint X z
  disjoint a b
  disjoint a x
  disjoint C a
  disjoint b x
  disjoint C b
  disjoint D a
  disjoint D b
  disjoint J a
  disjoint J b
  disjoint K a
  disjoint K b
  disjoint X a
  disjoint X b
  assert |- ( ( C e. ( *Met ` X ) /\ D e. ( *Met ` X ) ) -> ( J C_ K <-> A. x e. X A. r e. RR+ E. s e. RR+ ( x ( ball ` D ) s ) C_ ( x ( ball ` C ) r ) ) )

  proof
    cC
    cX
    cxmt
    cfv
    #
    wcel
    #
    cD
    @0
    wcel
    #
    wa
    #
    cJ
    cK
    wss
    cC
    cbl
    cfv
    #
    crn
    #
    ctg
    cfv
    #
    cD
    cbl
    cfv
    #
    crn
    #
    ctg
    cfv
    #
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    wcel
    #
    @11
    vz
    cv
    #
    wcel
    @14
    @12
    wss
    wa
    vz
    @8
    wrex
    #
    wi
    #
    vy
    @5
    wral
    #
    vx
    @5
    cuni
    #
    wral
    #
    @11
    vs
    cv
    @7
    co
    #
    @11
    vr
    cv
    #
    @4
    co
    #
    wss
    #
    vs
    crp
    wrex
    #
    vr
    crp
    wral
    #
    vx
    cX
    wral
    #
    @3
    cJ
    @6
    cK
    @9
    @1
    cJ
    @6
    wceq
    @2
    cC
    cJ
    cX
    metequiv.3
    mopnval
    adantr
    @2
    cK
    @9
    wceq
    @1
    cD
    cK
    cX
    metequiv.4
    mopnval
    adantl
    sseq12d
    @3
    @5
    ctb
    wcel
    #
    @18
    @8
    cuni
    #
    wceq
    @10
    @19
    wb
    @1
    @27
    @2
    cC
    cX
    blbas
    adantr
    @3
    @18
    cX
    @28
    @1
    @18
    cX
    wceq
    @2
    cC
    cX
    unirnbl
    adantr
    #
    @2
    @28
    cX
    wceq
    @1
    cD
    cX
    unirnbl
    adantl
    eqtr4d
    vx
    vy
    vz
    @5
    @8
    ctb
    tgss2
    syl2anc
    @3
    @19
    @17
    vx
    cX
    wral
    @26
    @3
    @17
    vx
    @18
    cX
    @29
    raleqdv
    @3
    @17
    @25
    vx
    cX
    @3
    @11
    cX
    wcel
    #
    wa
    #
    @17
    @13
    @20
    @12
    wss
    #
    vs
    crp
    wrex
    #
    wi
    #
    vy
    @5
    wral
    #
    @25
    @31
    @16
    @34
    vy
    @5
    @31
    @15
    @33
    @13
    @2
    @30
    @15
    @33
    wb
    @1
    vz
    @12
    cD
    @11
    cX
    vs
    blssex
    adantll
    imbi2d
    ralbidv
    @31
    @35
    @25
    @31
    @35
    @24
    vr
    crp
    @1
    @30
    @21
    crp
    wcel
    #
    @35
    @24
    wi
    #
    @2
    @1
    @30
    @36
    @37
    @1
    @30
    @36
    w3a
    @22
    @5
    wcel
    #
    @11
    @22
    wcel
    #
    @37
    @36
    @1
    @30
    @21
    cxr
    wcel
    @38
    @21
    rpxr
    cC
    @11
    @21
    cX
    blelrn
    syl3an3
    cC
    @11
    @21
    cX
    blcntr
    @38
    @35
    @39
    @24
    @34
    @39
    @24
    wi
    vy
    @22
    @5
    @12
    @22
    wceq
    #
    @13
    @39
    @33
    @24
    @12
    @22
    @11
    eleq2
    @40
    @32
    @23
    vs
    crp
    @12
    @22
    @20
    sseq2
    rexbidv
    imbi12d
    rspcv
    com23
    sylc
    3expa
    adantllr
    ralrimdva
    @31
    @25
    @34
    vy
    @5
    @31
    @12
    @5
    wcel
    #
    wa
    @13
    @25
    @33
    @31
    @41
    @13
    @25
    @33
    wi
    @31
    @41
    @13
    wa
    #
    wa
    @22
    @12
    wss
    #
    vr
    crp
    wrex
    #
    @25
    @33
    @3
    @42
    @44
    @30
    @1
    @42
    @44
    @2
    @1
    @41
    @13
    @44
    vr
    @12
    cC
    @11
    cX
    blss
    3expb
    adantlr
    adantlr
    @25
    @44
    @33
    @25
    @44
    wa
    @24
    @43
    wa
    #
    vr
    crp
    wrex
    @33
    @24
    @43
    vr
    crp
    r19.29
    @45
    @33
    vr
    crp
    @43
    @24
    @33
    @43
    @23
    @32
    vs
    crp
    @23
    @43
    @32
    @20
    @22
    @12
    sstr
    expcom
    reximdv
    impcom
    rexlimivw
    syl
    ex
    syl5com
    expr
    com23
    ralrimdva
    impbid
    bitrd
    ralbidva
    bitrd
    3bitrd
end
