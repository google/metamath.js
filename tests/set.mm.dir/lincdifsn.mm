include "clmod.mm"
include "wcel.mm"
include "cpw.mm"
include "w3a.mm"
include "cmap.mm"
include "co.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "wceq.mm"
include "clinc.mm"
include "cfv.mm"
include "cv.mm"
include "cvsca.mm"
include "cmpt.mm"
include "cgsu.mm"
include "csca.mm"
include "cbs.mm"
include "simp11.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "adantr.mm"
include "3ad2ant2.mm"
include "pweqi.mm"
include "3ad2ant1.mm"
include "lincval.mm"
include "syl3anc.mm"
include "ccmn.mm"
include "lmodcmn.mm"
include "simp12.mm"
include "c0g.mm"
include "anim2i.mm"
include "3adant3.mm"
include "simp2l.mm"
include "breq2i.mm"
include "adantl.mm"
include "scmfsupp.mm"
include "simpl1.mm"
include "wi.mm"
include "wf.mm"
include "elmapi.mm"
include "ffvelrn.mm"
include "ex.mm"
include "a1d.mm"
include "syl.mm"
include "impcom.mm"
include "imp.mm"
include "elelpwi.mm"
include "expcom.mm"
include "eqid.mm"
include "lmodvscl.mm"
include "3adantl3.mm"
include "simp13.mm"
include "3ad2ant3.mm"
include "syl5com.mm"
include "ancoms.mm"
include "3adant1.mm"
include "eqcomi.mm"
include "a1i.mm"
include "fveq2.mm"
include "id.mm"
include "oveq123d.mm"
include "gsumdifsnd.mm"
include "fveq1.mm"
include "fvres.mm"
include "sylan9eq.mm"
include "oveq1d.mm"
include "mpteq2dva.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "feq23i.mm"
include "sylib.mm"
include "difssd.mm"
include "fssresd.mm"
include "wb.mm"
include "feq1.mm"
include "mpbird.mm"
include "cvv.mm"
include "fvex.mm"
include "difexg.mm"
include "elmapg.mm"
include "sylancr.mm"
include "wss.mm"
include "elpwi.mm"
include "sseq2i.mm"
include "ssdifssd.mm"
include "elpwg.mm"
include "3eqtrd.mm"

theorem lincdifsn
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cM: class M
  let cV: class V
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
  let vk: setvar k
  assume lincdifsn.b: |- B = ( Base ` M )
  assume lincdifsn.r: |- R = ( Scalar ` M )
  assume lincdifsn.s: |- S = ( Base ` R )
  assume lincdifsn.t: |- .x. = ( .s ` M )
  assume lincdifsn.p: |- .+ = ( +g ` M )
  assume lincdifsn.0: |- .0. = ( 0g ` R )


  assert |- ( ( ( M e. LMod /\ V e. ~P B /\ X e. V ) /\ ( F e. ( S ^m V ) /\ F finSupp .0. ) /\ G = ( F |` ( V \ { X } ) ) ) -> ( F ( linC ` M ) V ) = ( ( G ( linC ` M ) ( V \ { X } ) ) .+ ( ( F ` X ) .x. X ) ) )

  proof
    cM
    clmod
    wcel
    #
    cV
    cB
    cpw
    #
    wcel
    #
    cX
    cV
    wcel
    #
    w3a
    #
    cF
    cS
    cV
    cmap
    co
    #
    wcel
    #
    cF
    c.0
    cfsupp
    wbr
    #
    wa
    #
    cG
    cF
    cV
    cX
    csn
    #
    cdif
    #
    cres
    #
    wceq
    #
    w3a
    #
    cF
    cV
    cM
    clinc
    cfv
    #
    co
    #
    cM
    vx
    cV
    vx
    cv
    #
    cF
    cfv
    #
    @16
    cM
    cvsca
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cM
    vx
    @10
    @16
    cG
    cfv
    #
    @16
    @18
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cX
    cF
    cfv
    #
    cX
    c.x
    co
    #
    c.pl
    co
    #
    cG
    @10
    @14
    co
    #
    @27
    c.pl
    co
    @13
    @0
    cF
    cM
    csca
    cfv
    #
    cbs
    cfv
    #
    cV
    cmap
    co
    #
    wcel
    #
    cV
    cM
    cbs
    cfv
    #
    cpw
    #
    wcel
    #
    @15
    @21
    wceq
    @0
    @2
    @3
    @8
    @12
    simp11
    #
    @8
    @4
    @33
    @12
    @6
    @33
    @7
    @6
    @33
    @5
    @32
    cF
    cS
    @31
    cV
    cmap
    cS
    cR
    cbs
    cfv
    @31
    lincdifsn.s
    cR
    @30
    cbs
    lincdifsn.r
    fveq2i
    eqtri
    #
    oveq1i
    eleq2i
    biimpi
    adantr
    3ad2ant2
    @4
    @8
    @36
    @12
    @2
    @0
    @36
    @3
    @2
    @36
    @1
    @35
    cV
    cB
    @34
    lincdifsn.b
    pweqi
    eleq2i
    biimpi
    #
    3ad2ant2
    3ad2ant1
    vx
    cF
    cM
    cV
    clmod
    lincval
    syl3anc
    @13
    @21
    cM
    vx
    @10
    @19
    cmpt
    #
    cgsu
    co
    #
    @27
    c.pl
    co
    @28
    @13
    cV
    cB
    c.pl
    vx
    cM
    cX
    @1
    @19
    @27
    lincdifsn.b
    lincdifsn.p
    @4
    @8
    cM
    ccmn
    wcel
    #
    @12
    @0
    @2
    @42
    @3
    cM
    lmodcmn
    3ad2ant1
    3ad2ant1
    @0
    @2
    @3
    @8
    @12
    simp12
    @13
    @0
    @36
    wa
    #
    @6
    cF
    cR
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    @20
    cM
    c0g
    cfv
    cfsupp
    wbr
    @4
    @8
    @43
    @12
    @0
    @2
    @43
    @3
    @2
    @36
    @0
    @39
    anim2i
    3adant3
    3ad2ant1
    @4
    @6
    @7
    @12
    simp2l
    @8
    @4
    @45
    @12
    @7
    @45
    @6
    @7
    @45
    c.0
    @44
    cF
    cfsupp
    lincdifsn.0
    breq2i
    biimpi
    adantl
    3ad2ant2
    vx
    cF
    cS
    cR
    cM
    cV
    lincdifsn.r
    lincdifsn.s
    scmfsupp
    syl3anc
    @4
    @8
    @16
    cV
    wcel
    #
    @19
    cB
    wcel
    #
    @12
    @4
    @8
    wa
    #
    @46
    wa
    @0
    @17
    cS
    wcel
    #
    @16
    cB
    wcel
    #
    @47
    @48
    @0
    @46
    @0
    @2
    @3
    @8
    simpl1
    #
    adantr
    @48
    @46
    @49
    @8
    @4
    @46
    @49
    wi
    #
    @6
    @4
    @52
    wi
    #
    @7
    @6
    cV
    cS
    cF
    wf
    #
    @53
    cF
    cS
    cV
    elmapi
    #
    @54
    @52
    @4
    @54
    @46
    @49
    cV
    cS
    @16
    cF
    ffvelrn
    ex
    a1d
    syl
    adantr
    impcom
    imp
    @48
    @46
    @50
    @4
    @46
    @50
    wi
    #
    @8
    @2
    @0
    @56
    @3
    @46
    @2
    @50
    @16
    cV
    cB
    elelpwi
    expcom
    3ad2ant2
    adantr
    imp
    @17
    @18
    cR
    cS
    cB
    cM
    @16
    lincdifsn.b
    lincdifsn.r
    @18
    eqid
    lincdifsn.s
    lmodvscl
    syl3anc
    3adantl3
    @0
    @2
    @3
    @8
    @12
    simp13
    @4
    @8
    @27
    cB
    wcel
    #
    @12
    @48
    @0
    @26
    cS
    wcel
    #
    cX
    cB
    wcel
    #
    @57
    @51
    @8
    @4
    @58
    @6
    @4
    @58
    wi
    @7
    @6
    @54
    @4
    @58
    @55
    @3
    @0
    @54
    @58
    wi
    @2
    @54
    @3
    @58
    cV
    cS
    cX
    cF
    ffvelrn
    expcom
    3ad2ant3
    syl5com
    adantr
    impcom
    @4
    @59
    @8
    @2
    @3
    @59
    @0
    @3
    @2
    @59
    cX
    cV
    cB
    elelpwi
    ancoms
    3adant1
    adantr
    @26
    c.x
    cR
    cS
    cB
    cM
    cX
    lincdifsn.b
    lincdifsn.r
    lincdifsn.t
    lincdifsn.s
    lmodvscl
    syl3anc
    3adant3
    @16
    cX
    wceq
    #
    @19
    @27
    wceq
    @13
    @60
    @17
    @26
    @16
    cX
    @18
    c.x
    @18
    c.x
    wceq
    @60
    c.x
    @18
    lincdifsn.t
    eqcomi
    a1i
    @16
    cX
    cF
    fveq2
    @60
    id
    oveq123d
    adantl
    gsumdifsnd
    @13
    @41
    @25
    @27
    c.pl
    @13
    @40
    @24
    cM
    cgsu
    @13
    @24
    @40
    @13
    vx
    @10
    @23
    @19
    @13
    @16
    @10
    wcel
    #
    wa
    @22
    @17
    @16
    @18
    @13
    @61
    @22
    @16
    @11
    cfv
    #
    @17
    @12
    @4
    @22
    @62
    wceq
    @8
    @16
    cG
    @11
    fveq1
    3ad2ant3
    @16
    @10
    cF
    fvres
    sylan9eq
    oveq1d
    mpteq2dva
    eqcomd
    oveq2d
    oveq1d
    eqtrd
    @13
    @25
    @29
    @27
    c.pl
    @13
    @29
    @25
    @13
    @0
    cG
    @31
    @10
    cmap
    co
    wcel
    #
    @10
    @35
    wcel
    #
    @29
    @25
    wceq
    @37
    @13
    @63
    @10
    @31
    cG
    wf
    #
    @13
    @65
    @10
    @31
    @11
    wf
    #
    @13
    cV
    @31
    @10
    cF
    @8
    @4
    cV
    @31
    cF
    wf
    #
    @12
    @6
    @67
    @7
    @6
    @54
    @67
    @55
    cV
    cS
    cV
    @31
    cF
    cV
    eqid
    @38
    feq23i
    sylib
    adantr
    3ad2ant2
    @13
    cV
    @9
    difssd
    fssresd
    @12
    @4
    @65
    @66
    wb
    @8
    @10
    @31
    cG
    @11
    feq1
    3ad2ant3
    mpbird
    @13
    @31
    cvv
    wcel
    @10
    cvv
    wcel
    #
    @63
    @65
    wb
    @30
    cbs
    fvex
    @4
    @8
    @68
    @12
    @2
    @0
    @68
    @3
    cV
    @9
    @1
    difexg
    #
    3ad2ant2
    3ad2ant1
    @31
    @10
    cG
    cvv
    cvv
    elmapg
    sylancr
    mpbird
    @4
    @8
    @64
    @12
    @0
    @2
    @64
    @3
    @0
    @2
    wa
    #
    @64
    @10
    @34
    wss
    #
    @2
    @71
    @0
    @2
    cV
    cB
    wss
    #
    @71
    cV
    cB
    elpwi
    @72
    cV
    @34
    @9
    @72
    cV
    @34
    wss
    cB
    @34
    cV
    lincdifsn.b
    sseq2i
    biimpi
    ssdifssd
    syl
    adantl
    @70
    @68
    @64
    @71
    wb
    @2
    @68
    @0
    @69
    adantl
    @10
    @34
    cvv
    elpwg
    syl
    mpbird
    3adant3
    3ad2ant1
    vx
    cG
    cM
    @10
    clmod
    lincval
    syl3anc
    eqcomd
    oveq1d
    3eqtrd
end
