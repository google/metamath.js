include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cxr.mm"
include "w3a.mm"
include "ccld.mm"
include "cuni.mm"
include "cdif.mm"
include "wceq.mm"
include "mopnuni.mm"
include "3ad2ant1.mm"
include "difeq1d.mm"
include "wss.mm"
include "cv.mm"
include "wa.mm"
include "cbl.mm"
include "crn.mm"
include "wrex.mm"
include "wral.mm"
include "difssd.mm"
include "clt.mm"
include "wbr.mm"
include "co.mm"
include "cq.mm"
include "simpl3.mm"
include "simpl1.mm"
include "simpl2.mm"
include "eldifi.mm"
include "adantl.mm"
include "xmetcl.mm"
include "syl3anc.mm"
include "cle.mm"
include "wn.mm"
include "eldif.mm"
include "oveq2.mm"
include "breq1d.mm"
include "elrab2.mm"
include "simplbi2.mm"
include "con3dimp.mm"
include "sylbi.mm"
include "wb.mm"
include "xrltnle.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "qbtwnxr.mm"
include "cr.mm"
include "wi.mm"
include "qre.mm"
include "cxne.mm"
include "cxad.mm"
include "adantr.mm"
include "rexr.mm"
include "ad2antrl.mm"
include "xnegcld.mm"
include "xaddcld.mm"
include "blelrn.mm"
include "cc0.mm"
include "simprrr.mm"
include "xposdif.mm"
include "mpbid.mm"
include "xblcntr.mm"
include "syl112anc.mm"
include "cin.mm"
include "c0.mm"
include "incom.mm"
include "xaddcom.mm"
include "simprl.mm"
include "xnpcan.mm"
include "eqtrd.mm"
include "xrleid.mm"
include "syl.mm"
include "eqbrtrd.mm"
include "bldisj.mm"
include "syl33anc.mm"
include "syl5eq.mm"
include "blssm.mm"
include "reldisj.mm"
include "simprrl.mm"
include "blsscls2.mm"
include "syl23anc.mm"
include "sscond.mm"
include "sstrd.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "expr.mm"
include "sylan2.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "elmopn.mm"
include "mpbir2and.mm"
include "eqeltrrd.mm"
include "ctop.mm"
include "mopntop.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "syl5sseq.mm"
include "eqid.mm"
include "iscld2.mm"

theorem blcld
  let vz: setvar z
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vr: setvar r
  let vw: setvar w
  let cN: class N
  let cT: class T
  assume mopni.1: |- J = ( MetOpen ` D )
  assume blcld.3: |- S = { z e. X | ( P D z ) <_ R }

  disjoint D z
  disjoint R z
  disjoint P z
  disjoint X z
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint D r
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint D w
  disjoint x z
  disjoint D x
  disjoint y z
  disjoint D y
  disjoint J r
  disjoint J x
  disjoint J y
  disjoint R x
  disjoint R y
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint N r
  disjoint N y
  disjoint P r
  disjoint P w
  disjoint P x
  disjoint P y
  disjoint T z
  disjoint X r
  disjoint X w
  disjoint X x
  disjoint X y
  assert |- ( ( D e. ( *Met ` X ) /\ P e. X /\ R e. RR* ) -> S e. ( Clsd ` J ) )

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
    cR
    cxr
    wcel
    #
    w3a
    #
    cS
    cJ
    ccld
    cfv
    wcel
    #
    cJ
    cuni
    #
    cS
    cdif
    #
    cJ
    wcel
    #
    @3
    cX
    cS
    cdif
    #
    @6
    cJ
    @3
    cX
    @5
    cS
    @0
    @1
    cX
    @5
    wceq
    @2
    cD
    cJ
    cX
    mopni.1
    mopnuni
    3ad2ant1
    #
    difeq1d
    @3
    @8
    cJ
    wcel
    #
    @8
    cX
    wss
    #
    vy
    cv
    #
    vw
    cv
    #
    wcel
    #
    @13
    @8
    wss
    #
    wa
    #
    vw
    cD
    cbl
    cfv
    #
    crn
    #
    wrex
    #
    vy
    @8
    wral
    #
    @3
    cX
    cS
    difssd
    @3
    @19
    vy
    @8
    @3
    @12
    @8
    wcel
    #
    wa
    #
    cR
    vx
    cv
    #
    clt
    wbr
    #
    @23
    cP
    @12
    cD
    co
    #
    clt
    wbr
    #
    wa
    #
    vx
    cq
    wrex
    #
    @19
    @22
    @2
    @25
    cxr
    wcel
    #
    cR
    @25
    clt
    wbr
    #
    @28
    @0
    @1
    @2
    @21
    simpl3
    #
    @22
    @0
    @1
    @12
    cX
    wcel
    #
    @29
    @0
    @1
    @2
    @21
    simpl1
    #
    @0
    @1
    @2
    @21
    simpl2
    #
    @21
    @32
    @3
    @12
    cX
    cS
    eldifi
    adantl
    #
    cP
    @12
    cD
    cX
    xmetcl
    syl3anc
    #
    @22
    @30
    @25
    cR
    cle
    wbr
    #
    wn
    #
    @21
    @38
    @3
    @21
    @32
    @12
    cS
    wcel
    #
    wn
    wa
    @38
    @12
    cX
    cS
    eldif
    @32
    @37
    @39
    @39
    @32
    @37
    cP
    vz
    cv
    #
    cD
    co
    #
    cR
    cle
    wbr
    #
    @37
    vz
    @12
    cX
    cS
    @40
    @12
    wceq
    @41
    @25
    cR
    cle
    @40
    @12
    cP
    cD
    oveq2
    breq1d
    blcld.3
    elrab2
    simplbi2
    con3dimp
    sylbi
    adantl
    @22
    @2
    @29
    @30
    @38
    wb
    @31
    @36
    cR
    @25
    xrltnle
    syl2anc
    mpbird
    vx
    cR
    @25
    qbtwnxr
    syl3anc
    @22
    @27
    @19
    vx
    cq
    @23
    cq
    wcel
    @22
    @23
    cr
    wcel
    #
    @27
    @19
    wi
    @23
    qre
    @22
    @43
    @27
    @19
    @22
    @43
    @27
    wa
    #
    wa
    #
    @12
    @25
    @23
    cxne
    #
    cxad
    co
    #
    @17
    co
    #
    @18
    wcel
    #
    @12
    @48
    wcel
    #
    @48
    @8
    wss
    #
    @19
    @45
    @0
    @32
    @47
    cxr
    wcel
    #
    @49
    @22
    @0
    @44
    @33
    adantr
    #
    @22
    @32
    @44
    @35
    adantr
    #
    @45
    @25
    @46
    @22
    @29
    @44
    @36
    adantr
    #
    @45
    @23
    @43
    @23
    cxr
    wcel
    #
    @22
    @27
    @23
    rexr
    ad2antrl
    #
    xnegcld
    xaddcld
    #
    cD
    @12
    @47
    cX
    blelrn
    syl3anc
    @45
    @0
    @32
    @52
    cc0
    @47
    clt
    wbr
    #
    @50
    @53
    @54
    @58
    @45
    @26
    @59
    @22
    @43
    @24
    @26
    simprrr
    @45
    @56
    @29
    @26
    @59
    wb
    @57
    @55
    @23
    @25
    xposdif
    syl2anc
    mpbid
    cD
    @12
    @47
    cX
    xblcntr
    syl112anc
    @45
    @48
    cX
    cP
    @23
    @17
    co
    #
    cdif
    #
    @8
    @45
    @48
    @60
    cin
    #
    c0
    wceq
    #
    @48
    @61
    wss
    #
    @45
    @62
    @60
    @48
    cin
    #
    c0
    @48
    @60
    incom
    @45
    @0
    @1
    @32
    @56
    @52
    @23
    @47
    cxad
    co
    #
    @25
    cle
    wbr
    @65
    c0
    wceq
    @53
    @22
    @1
    @44
    @34
    adantr
    #
    @54
    @57
    @58
    @45
    @66
    @25
    @25
    cle
    @45
    @66
    @47
    @23
    cxad
    co
    #
    @25
    @45
    @56
    @52
    @66
    @68
    wceq
    @57
    @58
    @23
    @47
    xaddcom
    syl2anc
    @45
    @29
    @43
    @68
    @25
    wceq
    @55
    @22
    @43
    @27
    simprl
    @25
    @23
    xnpcan
    syl2anc
    eqtrd
    @45
    @29
    @25
    @25
    cle
    wbr
    @55
    @25
    xrleid
    syl
    eqbrtrd
    cD
    cP
    @12
    @23
    @47
    cX
    bldisj
    syl33anc
    syl5eq
    @45
    @48
    cX
    wss
    #
    @63
    @64
    wb
    @45
    @0
    @32
    @52
    @69
    @53
    @54
    @58
    cD
    @12
    @47
    cX
    blssm
    syl3anc
    @48
    @60
    cX
    reldisj
    syl
    mpbid
    @45
    cS
    @60
    cX
    @45
    @0
    @1
    @2
    @56
    @24
    cS
    @60
    wss
    @53
    @67
    @22
    @2
    @44
    @31
    adantr
    @57
    @22
    @43
    @24
    @26
    simprrl
    vz
    cD
    cP
    cR
    cS
    @23
    cJ
    cX
    mopni.1
    blcld.3
    blsscls2
    syl23anc
    sscond
    sstrd
    @16
    @50
    @51
    wa
    vw
    @48
    @18
    @13
    @48
    wceq
    @14
    @50
    @15
    @51
    @13
    @48
    @12
    eleq2
    @13
    @48
    @8
    sseq1
    anbi12d
    rspcev
    syl12anc
    expr
    sylan2
    rexlimdva
    mpd
    ralrimiva
    @0
    @1
    @10
    @11
    @20
    wa
    wb
    @2
    vy
    vw
    @8
    cD
    cJ
    cX
    mopni.1
    elmopn
    3ad2ant1
    mpbir2and
    eqeltrrd
    @3
    cJ
    ctop
    wcel
    #
    cS
    @5
    wss
    @4
    @7
    wb
    @0
    @1
    @70
    @2
    cD
    cJ
    cX
    mopni.1
    mopntop
    3ad2ant1
    @3
    cX
    cS
    @5
    cS
    @42
    vz
    cX
    crab
    cX
    blcld.3
    @42
    vz
    cX
    ssrab2
    eqsstri
    @9
    syl5sseq
    cS
    cJ
    @5
    @5
    eqid
    iscld2
    syl2anc
    mpbird
end
