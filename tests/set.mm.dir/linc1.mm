include "clmod.mm"
include "wcel.mm"
include "cpw.mm"
include "w3a.mm"
include "clinc.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "cvsca.mm"
include "cmpt.mm"
include "cgsu.mm"
include "csca.mm"
include "cbs.mm"
include "cmap.mm"
include "wceq.mm"
include "simp1.mm"
include "wf.mm"
include "cif.mm"
include "wa.mm"
include "crg.mm"
include "lmodring.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "ringidcl.mm"
include "ring0cl.mm"
include "jca.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "ifcl.mm"
include "fmptd.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "simp2.mm"
include "elmapg.mm"
include "sylancr.mm"
include "mpbird.mm"
include "pweqi.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "3ad2ant2.mm"
include "lincval.mm"
include "syl3anc.mm"
include "c0g.mm"
include "eqid.mm"
include "cmnd.mm"
include "cgrp.mm"
include "lmodgrp.mm"
include "grpmnd.mm"
include "simp3.mm"
include "simpr.mm"
include "lmod1cl.mm"
include "lmod0cl.mm"
include "ifcld.mm"
include "weq.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "wi.mm"
include "elelpwi.mm"
include "expcom.mm"
include "imp.mm"
include "lmodvscl.mm"
include "csupp.mm"
include "wne.mm"
include "crab.mm"
include "csn.mm"
include "fveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "cbvmptv.mm"
include "fvexd.mm"
include "ovexd.mm"
include "mptsuppd.mm"
include "wral.mm"
include "wss.mm"
include "2a1.mm"
include "wn.mm"
include "simprr.mm"
include "cur.mm"
include "eqeltri.mm"
include "ifex.mm"
include "sylancl.mm"
include "iffalse.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "adantl.mm"
include "lmod0vs.mm"
include "neeq1d.mm"
include "eqneqall.mm"
include "ax-mp.mm"
include "syl6bi.mm"
include "ex.mm"
include "pm2.61i.mm"
include "ralrimiva.mm"
include "rabsssn.mm"
include "sylibr.mm"
include "eqsstrd.mm"
include "gsumpt.mm"
include "ovex.mm"
include "iftrue.mm"
include "ancoms.mm"
include "3adant1.mm"
include "lmodvs1.mm"
include "3eqtrd.mm"

theorem linc1
  let vx: setvar x
  let cB: class B
  let cS: class S
  let c.1: class .1.
  let cF: class F
  let cM: class M
  let cV: class V
  let cX: class X
  let c.0: class .0.
  let vv: setvar v
  let vy: setvar y
  let vk: setvar k
  assume linc1.b: |- B = ( Base ` M )
  assume linc1.s: |- S = ( Scalar ` M )
  assume linc1.0: |- .0. = ( 0g ` S )
  assume linc1.1: |- .1. = ( 1r ` S )
  assume linc1.f: |- F = ( x e. V |-> if ( x = X , .1. , .0. ) )

  disjoint B x
  disjoint M x
  disjoint V x
  disjoint X x
  disjoint .0. x
  disjoint .1. x
  disjoint B v
  disjoint B y
  disjoint v x
  disjoint v y
  disjoint x y
  disjoint F v
  disjoint F y
  disjoint M v
  disjoint M y
  disjoint V v
  disjoint V y
  disjoint X v
  disjoint X y
  disjoint k x
  assert |- ( ( M e. LMod /\ V e. ~P B /\ X e. V ) -> ( F ( linC ` M ) V ) = X )

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
    cV
    cM
    clinc
    cfv
    co
    #
    cM
    vy
    cV
    vy
    cv
    #
    cF
    cfv
    #
    @6
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
    cX
    @10
    cfv
    #
    cX
    @4
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
    @5
    @11
    wceq
    @0
    @2
    @3
    simp1
    #
    @4
    @15
    cV
    @14
    cF
    wf
    #
    @4
    vx
    cV
    vx
    cv
    #
    cX
    wceq
    #
    c.1
    c.0
    cif
    #
    @14
    cF
    @4
    @21
    cV
    wcel
    #
    wa
    c.1
    @14
    wcel
    #
    c.0
    @14
    wcel
    #
    wa
    #
    @23
    @14
    wcel
    @4
    @27
    @24
    @0
    @2
    @27
    @3
    @0
    cS
    crg
    wcel
    #
    @27
    cS
    cM
    linc1.s
    lmodring
    @28
    @25
    @26
    @14
    cS
    c.1
    @13
    cS
    cbs
    cS
    @13
    linc1.s
    eqcomi
    fveq2i
    #
    linc1.1
    ringidcl
    @14
    cS
    c.0
    @29
    linc1.0
    ring0cl
    jca
    syl
    3ad2ant1
    adantr
    @22
    c.1
    c.0
    @14
    ifcl
    syl
    linc1.f
    fmptd
    @4
    @14
    cvv
    wcel
    @2
    @15
    @20
    wb
    @13
    cbs
    fvex
    @0
    @2
    @3
    simp2
    #
    @14
    cV
    cF
    cvv
    @1
    elmapg
    sylancr
    mpbird
    @2
    @0
    @18
    @3
    @2
    @18
    @1
    @17
    cV
    cB
    @16
    linc1.b
    pweqi
    eleq2i
    biimpi
    3ad2ant2
    vy
    cF
    cM
    cV
    clmod
    lincval
    syl3anc
    @4
    cV
    cB
    @10
    cM
    @1
    cX
    cM
    c0g
    cfv
    #
    linc1.b
    @31
    eqid
    #
    @0
    @2
    cM
    cmnd
    wcel
    #
    @3
    @0
    cM
    cgrp
    wcel
    @33
    cM
    lmodgrp
    cM
    grpmnd
    syl
    3ad2ant1
    @30
    @0
    @2
    @3
    simp3
    #
    @4
    vy
    cV
    @9
    cB
    @10
    @4
    @6
    cV
    wcel
    #
    wa
    #
    @0
    @7
    cS
    cbs
    cfv
    #
    wcel
    @6
    cB
    wcel
    #
    @9
    cB
    wcel
    @4
    @0
    @35
    @19
    adantr
    @36
    @7
    @6
    cX
    wceq
    #
    c.1
    c.0
    cif
    #
    @37
    @36
    @35
    @40
    @37
    wcel
    @7
    @40
    wceq
    @4
    @35
    simpr
    @36
    @39
    c.1
    c.0
    @37
    @4
    c.1
    @37
    wcel
    #
    @35
    @0
    @2
    @41
    @3
    c.1
    cS
    @37
    cM
    linc1.s
    @37
    eqid
    #
    linc1.1
    lmod1cl
    3ad2ant1
    adantr
    @4
    c.0
    @37
    wcel
    #
    @35
    @0
    @2
    @43
    @3
    cS
    @37
    cM
    c.0
    linc1.s
    @42
    linc1.0
    lmod0cl
    3ad2ant1
    adantr
    ifcld
    #
    vx
    @6
    @23
    @40
    cV
    @37
    cF
    vx
    vy
    weq
    @22
    @39
    c.1
    c.0
    @21
    @6
    cX
    eqeq1
    ifbid
    linc1.f
    fvmptg
    syl2anc
    @44
    eqeltrd
    @4
    @35
    @38
    @2
    @0
    @35
    @38
    wi
    @3
    @35
    @2
    @38
    @6
    cV
    cB
    elelpwi
    expcom
    3ad2ant2
    imp
    @7
    @8
    cS
    @37
    cB
    cM
    @6
    linc1.b
    linc1.s
    @8
    eqid
    #
    @42
    lmodvscl
    syl3anc
    @10
    eqid
    #
    fmptd
    @4
    @10
    @31
    csupp
    co
    vv
    cv
    #
    cF
    cfv
    #
    @47
    @8
    co
    #
    @31
    wne
    #
    vv
    cV
    crab
    #
    cX
    csn
    #
    @4
    vv
    cV
    @49
    cvv
    @10
    @1
    cvv
    @31
    vy
    vv
    cV
    @9
    @49
    vy
    vv
    weq
    #
    @7
    @48
    @6
    @47
    @8
    @6
    @47
    cF
    fveq2
    @53
    id
    oveq12d
    cbvmptv
    @30
    @4
    cM
    c0g
    fvexd
    @4
    @47
    cV
    wcel
    #
    wa
    #
    @48
    @47
    @8
    ovexd
    mptsuppd
    @4
    @50
    @47
    cX
    wceq
    #
    wi
    #
    vv
    cV
    wral
    @51
    @52
    wss
    @4
    @57
    vv
    cV
    @56
    @55
    @57
    wi
    @56
    @55
    @50
    2a1
    @56
    wn
    #
    @55
    @57
    @58
    @55
    wa
    #
    @50
    @31
    @31
    wne
    #
    @56
    @59
    @49
    @31
    @31
    @59
    @49
    c.0
    @47
    @8
    co
    #
    @31
    @59
    @48
    c.0
    @47
    @8
    @59
    @48
    @56
    c.1
    c.0
    cif
    #
    c.0
    @59
    @54
    @62
    cvv
    wcel
    @48
    @62
    wceq
    @58
    @4
    @54
    simprr
    @56
    c.1
    c.0
    c.1
    cS
    cur
    cfv
    cvv
    linc1.1
    cS
    cur
    fvex
    eqeltri
    #
    c.0
    cS
    c0g
    cfv
    cvv
    linc1.0
    cS
    c0g
    fvex
    eqeltri
    ifex
    vx
    @47
    @23
    @62
    cV
    cvv
    cF
    vx
    vv
    weq
    @22
    @56
    c.1
    c.0
    @21
    @47
    cX
    eqeq1
    ifbid
    linc1.f
    fvmptg
    sylancl
    @58
    @62
    c.0
    wceq
    @55
    @56
    c.1
    c.0
    iffalse
    adantr
    eqtrd
    oveq1d
    @59
    @0
    @47
    cB
    wcel
    #
    @61
    @31
    wceq
    @55
    @0
    @58
    @4
    @0
    @54
    @19
    adantr
    adantl
    @55
    @64
    @58
    @4
    @54
    @64
    @2
    @0
    @54
    @64
    wi
    @3
    @54
    @2
    @64
    @47
    cV
    cB
    elelpwi
    expcom
    3ad2ant2
    imp
    adantl
    @8
    cS
    c.0
    cB
    cM
    @47
    @31
    linc1.b
    linc1.s
    @45
    linc1.0
    @32
    lmod0vs
    syl2anc
    eqtrd
    neeq1d
    @31
    @31
    wceq
    @60
    @56
    wi
    @32
    @56
    @31
    @31
    eqneqall
    ax-mp
    syl6bi
    ex
    pm2.61i
    ralrimiva
    @50
    vv
    cV
    cX
    rabsssn
    sylibr
    eqsstrd
    gsumpt
    @4
    @12
    cX
    cF
    cfv
    #
    cX
    @8
    co
    #
    c.1
    cX
    @8
    co
    #
    cX
    @4
    @3
    @66
    cvv
    wcel
    @12
    @66
    wceq
    @34
    @65
    cX
    @8
    ovex
    vy
    cX
    @9
    @66
    cV
    cvv
    @10
    @39
    @7
    @65
    @6
    cX
    @8
    @6
    cX
    cF
    fveq2
    @39
    id
    oveq12d
    @46
    fvmptg
    sylancl
    @4
    @65
    c.1
    cX
    @8
    @4
    @3
    c.1
    cvv
    wcel
    @65
    c.1
    wceq
    @34
    @63
    vx
    cX
    @23
    c.1
    cV
    cvv
    cF
    @22
    c.1
    c.0
    iftrue
    linc1.f
    fvmptg
    sylancl
    oveq1d
    @4
    @0
    cX
    cB
    wcel
    #
    @67
    cX
    wceq
    @19
    @2
    @3
    @68
    @0
    @3
    @2
    @68
    cX
    cV
    cB
    elelpwi
    ancoms
    3adant1
    @8
    c.1
    cS
    cB
    cM
    cX
    linc1.b
    linc1.s
    @45
    linc1.1
    lmodvs1
    syl2anc
    3eqtrd
    3eqtrd
end
