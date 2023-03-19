include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cbnd.mm"
include "cv.mm"
include "cbl.mm"
include "co.mm"
include "wss.mm"
include "cr.mm"
include "wrex.mm"
include "c0.mm"
include "wceq.mm"
include "wi.mm"
include "wne.mm"
include "wral.mm"
include "cc0.mm"
include "0re.mm"
include "ne0ii.mm"
include "0ss.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "ralrimivw.mm"
include "r19.2z.mm"
include "sylancr.mm"
include "a1i.mm"
include "cxmt.mm"
include "crp.mm"
include "isbnd2.mm"
include "caddc.mm"
include "simplll.mm"
include "cxp.mm"
include "cdm.mm"
include "cin.mm"
include "cres.mm"
include "dmeqi.mm"
include "dmres.mm"
include "eqtri.mm"
include "cxr.mm"
include "wf.mm"
include "xmetf.mm"
include "fdm.mm"
include "syl.mm"
include "syl5eqr.mm"
include "df-ss.mm"
include "sylibr.mm"
include "ad2antlr.mm"
include "metf.mm"
include "ad3antrrr.mm"
include "sseqtrd.mm"
include "dmss.mm"
include "dmxpid.mm"
include "3sstr3g.mm"
include "simprl.mm"
include "sseldd.mm"
include "simpllr.mm"
include "metcl.mm"
include "syl3anc.mm"
include "rpre.mm"
include "ad2antll.mm"
include "readdcld.mm"
include "metxmet.mm"
include "elind.mm"
include "rpxr.mm"
include "blres.mm"
include "inss1.mm"
include "cmin.mm"
include "cle.mm"
include "wbr.mm"
include "leidd.mm"
include "recnd.mm"
include "pncand.mm"
include "breqtrrd.mm"
include "blss2.mm"
include "syl33anc.mm"
include "syl5ss.mm"
include "eqsstrd.mm"
include "oveq2.mm"
include "sseq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rexbidv.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "expdimp.mm"
include "pm2.61dne.mm"
include "ex.mm"
include "simprr.mm"
include "xpss12.mm"
include "resabs1d.mm"
include "syl6eqr.mm"
include "blbnd.mm"
include "syl3an1.mm"
include "3expa.mm"
include "adantrr.mm"
include "bndss.mm"
include "eqeltrrd.mm"
include "rexlimdvaa.mm"
include "impbid.mm"

theorem ssbnd
  let cP: class P
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vd: setvar d
  let vm: setvar m
  let vr: setvar r
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cR: class R
  let cS: class S
  assume ssbnd.2: |- N = ( M |` ( Y X. Y ) )

  disjoint M d
  disjoint N d
  disjoint P d
  disjoint X d
  disjoint Y d
  disjoint d m
  disjoint d r
  disjoint d s
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint m r
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint M m
  disjoint r s
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint M r
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint M s
  disjoint x y
  disjoint x z
  disjoint M x
  disjoint y z
  disjoint M y
  disjoint M z
  disjoint N r
  disjoint N y
  disjoint P r
  disjoint P y
  disjoint X m
  disjoint X r
  disjoint X s
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint R r
  disjoint R x
  disjoint S r
  disjoint S x
  disjoint Y r
  disjoint Y x
  disjoint Y y
  assert |- ( ( M e. ( Met ` X ) /\ P e. X ) -> ( N e. ( Bnd ` Y ) <-> E. d e. RR Y C_ ( P ( ball ` M ) d ) ) )

  proof
    cM
    cX
    cme
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
    cY
    cbnd
    cfv
    #
    wcel
    #
    cY
    cP
    vd
    cv
    #
    cM
    cbl
    cfv
    #
    co
    #
    wss
    #
    vd
    cr
    wrex
    #
    @2
    @4
    @9
    @2
    @4
    wa
    #
    @9
    cY
    c0
    cY
    c0
    wceq
    #
    @9
    wi
    @10
    @11
    cr
    c0
    wne
    @8
    vd
    cr
    wral
    @9
    cc0
    cr
    0re
    ne0ii
    @11
    @8
    vd
    cr
    @11
    @8
    c0
    @7
    wss
    @7
    0ss
    cY
    c0
    @7
    sseq1
    mpbiri
    ralrimivw
    @8
    vd
    cr
    r19.2z
    sylancr
    a1i
    @2
    @4
    cY
    c0
    wne
    #
    @9
    @4
    @12
    wa
    cN
    cY
    cxmt
    cfv
    wcel
    #
    cY
    vy
    cv
    #
    vr
    cv
    #
    cN
    cbl
    cfv
    co
    #
    wceq
    #
    vr
    crp
    wrex
    vy
    cY
    wrex
    #
    wa
    @2
    @9
    vy
    cN
    cY
    vr
    isbnd2
    @2
    @13
    @18
    @9
    @2
    @13
    wa
    #
    @17
    @9
    vy
    vr
    cY
    crp
    @19
    @14
    cY
    wcel
    #
    @15
    crp
    wcel
    #
    wa
    #
    wa
    #
    @9
    @17
    @16
    @7
    wss
    #
    vd
    cr
    wrex
    #
    @23
    @14
    cP
    cM
    co
    #
    @15
    caddc
    co
    #
    cr
    wcel
    #
    @16
    cP
    @27
    @6
    co
    #
    wss
    #
    @25
    @23
    @26
    @15
    @23
    @0
    @14
    cX
    wcel
    #
    @1
    @26
    cr
    wcel
    @0
    @1
    @13
    @22
    simplll
    #
    @23
    cY
    cX
    @14
    @23
    cY
    cY
    cxp
    #
    cdm
    #
    cX
    cX
    cxp
    #
    cdm
    #
    cY
    cX
    @23
    @33
    @35
    wss
    @34
    @36
    wss
    @23
    @33
    cM
    cdm
    #
    @35
    @13
    @33
    @37
    wss
    #
    @2
    @22
    @13
    @33
    @37
    cin
    #
    @33
    wceq
    @38
    @13
    @39
    cN
    cdm
    #
    @33
    @40
    cM
    @33
    cres
    #
    cdm
    @39
    cN
    @41
    ssbnd.2
    dmeqi
    cM
    @33
    dmres
    eqtri
    @13
    @33
    cxr
    cN
    wf
    @40
    @33
    wceq
    cN
    cY
    xmetf
    @33
    cxr
    cN
    fdm
    syl
    syl5eqr
    @33
    @37
    df-ss
    sylibr
    ad2antlr
    @0
    @37
    @35
    wceq
    #
    @1
    @13
    @22
    @0
    @35
    cr
    cM
    wf
    @42
    cM
    cX
    metf
    @35
    cr
    cM
    fdm
    syl
    ad3antrrr
    sseqtrd
    @33
    @35
    dmss
    syl
    cY
    dmxpid
    cX
    dmxpid
    3sstr3g
    @19
    @20
    @21
    simprl
    #
    sseldd
    #
    @0
    @1
    @13
    @22
    simpllr
    #
    @14
    cP
    cM
    cX
    metcl
    syl3anc
    #
    @21
    @15
    cr
    wcel
    #
    @19
    @20
    @15
    rpre
    ad2antll
    #
    readdcld
    #
    @23
    @16
    @14
    @15
    @6
    co
    #
    cY
    cin
    #
    @29
    @23
    cM
    cX
    cxmt
    cfv
    wcel
    #
    @14
    cX
    cY
    cin
    wcel
    @15
    cxr
    wcel
    #
    @16
    @51
    wceq
    @23
    @0
    @52
    @32
    cM
    cX
    metxmet
    #
    syl
    #
    @23
    cX
    cY
    @14
    @44
    @43
    elind
    @21
    @53
    @19
    @20
    @15
    rpxr
    ad2antll
    cN
    cM
    @14
    @15
    cX
    cY
    ssbnd.2
    blres
    syl3anc
    @23
    @51
    @50
    @29
    @50
    cY
    inss1
    @23
    @52
    @31
    @1
    @47
    @28
    @26
    @27
    @15
    cmin
    co
    #
    cle
    wbr
    @50
    @29
    wss
    @55
    @44
    @45
    @48
    @49
    @23
    @26
    @26
    @56
    cle
    @23
    @26
    @46
    leidd
    @23
    @26
    @15
    @23
    @26
    @46
    recnd
    @23
    @15
    @48
    recnd
    pncand
    breqtrrd
    cM
    @14
    cP
    @15
    @27
    cX
    blss2
    syl33anc
    syl5ss
    eqsstrd
    @24
    @30
    vd
    @27
    cr
    @5
    @27
    wceq
    @7
    @29
    @16
    @5
    @27
    cP
    @6
    oveq2
    sseq2d
    rspcev
    syl2anc
    @17
    @8
    @24
    vd
    cr
    cY
    @16
    @7
    sseq1
    rexbidv
    syl5ibrcom
    rexlimdvva
    expimpd
    syl5bi
    expdimp
    pm2.61dne
    ex
    @2
    @8
    @4
    vd
    cr
    @2
    @5
    cr
    wcel
    #
    @8
    wa
    wa
    #
    cM
    @7
    @7
    cxp
    #
    cres
    #
    @33
    cres
    #
    cN
    @3
    @58
    @61
    @41
    cN
    @58
    cM
    @33
    @59
    @58
    @8
    @8
    @33
    @59
    wss
    @2
    @57
    @8
    simprr
    #
    @62
    cY
    @7
    cY
    @7
    xpss12
    syl2anc
    resabs1d
    ssbnd.2
    syl6eqr
    @58
    @60
    @7
    cbnd
    cfv
    wcel
    #
    @8
    @61
    @3
    wcel
    @2
    @57
    @63
    @8
    @0
    @1
    @57
    @63
    @0
    @52
    @1
    @57
    @63
    @54
    @5
    cM
    cX
    cP
    blbnd
    syl3an1
    3expa
    adantrr
    @62
    cY
    @60
    @7
    bndss
    syl2anc
    eqeltrrd
    rexlimdvaa
    impbid
end
