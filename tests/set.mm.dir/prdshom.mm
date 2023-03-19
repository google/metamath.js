include "cds.mm"
include "cfv.mm"
include "cplusg.mm"
include "cxp.mm"
include "cv.mm"
include "c2nd.mm"
include "chom.mm"
include "co.mm"
include "cixp.mm"
include "cmpt2.mm"
include "c1st.mm"
include "cop.mm"
include "cco.mm"
include "cmpt.mm"
include "cvsca.mm"
include "cmulr.mm"
include "cip.mm"
include "cgsu.mm"
include "cple.mm"
include "cts.mm"
include "cbs.mm"
include "eqid.mm"
include "prdsbas.mm"
include "prdsplusg.mm"
include "prdsmulr.mm"
include "prdsvsca.mm"
include "eqidd.mm"
include "prdstset.mm"
include "prdsle.mm"
include "prdsds.mm"
include "prdsval.mm"
include "homid.mm"
include "crn.mm"
include "cuni.mm"
include "cmap.mm"
include "cpw.mm"
include "wf.mm"
include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "wss.mm"
include "ovssunirn.mm"
include "cnx.mm"
include "strfvss.mm"
include "fvssunirn.mm"
include "rnss.mm"
include "uniss.mm"
include "mp2b.mm"
include "sstri.mm"
include "rgenw.mm"
include "ss2ixp.mm"
include "ax-mp.mm"
include "wceq.mm"
include "cdm.mm"
include "dmexg.mm"
include "syl.mm"
include "eqeltrrd.mm"
include "rnexg.mm"
include "uniexg.mm"
include "3syl.mm"
include "ixpconstg.mm"
include "syl2anc.mm"
include "syl5sseq.mm"
include "ovex.mm"
include "elpw2.mm"
include "sylibr.mm"
include "ralrimivw.mm"
include "fmpt2.mm"
include "sylib.mm"
include "fvex.mm"
include "eqeltri.mm"
include "xpex.mm"
include "a1i.mm"
include "pwex.mm"
include "fex2.mm"
include "syl3anc.mm"
include "csn.mm"
include "ctp.mm"
include "cpr.mm"
include "cun.mm"
include "csca.mm"
include "snsspr1.mm"
include "ssun2.mm"
include "prdsvallem.mm"

theorem prdshom
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  let cI: class I
  let cV: class V
  let cW: class W
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let cK: class K
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume prdsbas.p: |- P = ( S Xs_ R )
  assume prdsbas.s: |- ( ph -> S e. V )
  assume prdsbas.r: |- ( ph -> R e. W )
  assume prdsbas.b: |- B = ( Base ` P )
  assume prdsbas.i: |- ( ph -> dom R = I )
  assume prdshom.h: |- H = ( Hom ` P )

  disjoint f g
  disjoint f x
  disjoint B f
  disjoint g x
  disjoint B g
  disjoint B x
  disjoint f ph
  disjoint g ph
  disjoint ph x
  disjoint I f
  disjoint I g
  disjoint I x
  disjoint P f
  disjoint P g
  disjoint P x
  disjoint R f
  disjoint R g
  disjoint R x
  disjoint S f
  disjoint S g
  disjoint S x
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a f
  disjoint a g
  disjoint a x
  disjoint B a
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint c g
  disjoint c x
  disjoint B c
  disjoint d e
  disjoint d f
  disjoint d g
  disjoint d x
  disjoint B d
  disjoint e f
  disjoint e g
  disjoint e x
  disjoint B e
  disjoint H a
  disjoint H c
  disjoint H d
  disjoint H e
  disjoint K f
  disjoint K g
  disjoint a ph
  disjoint c ph
  disjoint d ph
  disjoint e ph
  disjoint a w
  disjoint a y
  disjoint a z
  disjoint I a
  disjoint c w
  disjoint c y
  disjoint c z
  disjoint I c
  disjoint d w
  disjoint d y
  disjoint d z
  disjoint I d
  disjoint e w
  disjoint e y
  disjoint e z
  disjoint I e
  disjoint f w
  disjoint f y
  disjoint f z
  disjoint g w
  disjoint g y
  disjoint g z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint I w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint I y
  disjoint I z
  disjoint R a
  disjoint R c
  disjoint R d
  disjoint R e
  disjoint R w
  disjoint R y
  disjoint R z
  disjoint S a
  disjoint S c
  disjoint S d
  disjoint S e
  assert |- ( ph -> H = ( f e. B , g e. B |-> X_ x e. I ( ( f ` x ) ( Hom ` ( R ` x ) ) ( g ` x ) ) ) )

  proof
    wph
    cH
    cB
    cP
    cds
    cfv
    #
    cP
    cplusg
    cfv
    #
    cS
    va
    vc
    cB
    cB
    cxp
    #
    cB
    vd
    ve
    vc
    cv
    #
    va
    cv
    #
    c2nd
    cfv
    #
    vf
    vg
    cB
    cB
    vx
    cI
    vx
    cv
    #
    vf
    cv
    cfv
    #
    @6
    vg
    cv
    cfv
    #
    @6
    cR
    cfv
    #
    chom
    cfv
    #
    co
    #
    cixp
    #
    cmpt2
    #
    co
    @4
    @13
    cfv
    vx
    cI
    @6
    vd
    cv
    cfv
    @6
    ve
    cv
    cfv
    @6
    @4
    c1st
    cfv
    cfv
    @6
    @5
    cfv
    cop
    @6
    @3
    cfv
    @9
    cco
    cfv
    co
    co
    cmpt
    cmpt2
    cmpt2
    #
    @13
    cP
    cvsca
    cfv
    #
    cP
    cmulr
    cfv
    #
    cP
    chom
    @13
    vf
    vg
    cB
    cB
    cS
    vx
    cI
    @7
    @8
    @9
    cip
    cfv
    co
    cmpt
    cgsu
    co
    cmpt2
    #
    cP
    cple
    cfv
    #
    cP
    cts
    cfv
    #
    wph
    vx
    cB
    @0
    cP
    @1
    cR
    cS
    @14
    @15
    @16
    ve
    vf
    vg
    @13
    @17
    cI
    cS
    cbs
    cfv
    #
    @18
    @19
    cV
    cW
    va
    vc
    vd
    prdsbas.p
    @20
    eqid
    #
    prdsbas.i
    wph
    vx
    cB
    cP
    cR
    cS
    cI
    cV
    cW
    prdsbas.p
    prdsbas.s
    prdsbas.r
    prdsbas.b
    prdsbas.i
    prdsbas
    wph
    vx
    cB
    cP
    @1
    cR
    cS
    vf
    vg
    cI
    cV
    cW
    prdsbas.p
    prdsbas.s
    prdsbas.r
    prdsbas.b
    prdsbas.i
    @1
    eqid
    prdsplusg
    wph
    vx
    cB
    cP
    cR
    cS
    @16
    vf
    vg
    cI
    cV
    cW
    prdsbas.p
    prdsbas.s
    prdsbas.r
    prdsbas.b
    prdsbas.i
    @16
    eqid
    prdsmulr
    wph
    vx
    cB
    cP
    cR
    cS
    @15
    vf
    vg
    cI
    @20
    cV
    cW
    prdsbas.p
    prdsbas.s
    prdsbas.r
    prdsbas.b
    prdsbas.i
    @21
    @15
    eqid
    prdsvsca
    wph
    @17
    eqidd
    wph
    cB
    cP
    cR
    cS
    cI
    @19
    cV
    cW
    prdsbas.p
    prdsbas.s
    prdsbas.r
    prdsbas.b
    prdsbas.i
    @19
    eqid
    prdstset
    wph
    vx
    cB
    cP
    cR
    cS
    vf
    vg
    cI
    @18
    cV
    cW
    prdsbas.p
    prdsbas.s
    prdsbas.r
    prdsbas.b
    prdsbas.i
    @18
    eqid
    prdsle
    wph
    vx
    cB
    @0
    cP
    cR
    cS
    vf
    vg
    cI
    cV
    cW
    prdsbas.p
    prdsbas.s
    prdsbas.r
    prdsbas.b
    prdsbas.i
    @0
    eqid
    prdsds
    wph
    @13
    eqidd
    wph
    @14
    eqidd
    prdsbas.s
    prdsbas.r
    prdsval
    prdshom.h
    homid
    wph
    @2
    cR
    crn
    #
    cuni
    #
    crn
    #
    cuni
    #
    crn
    #
    cuni
    #
    cI
    cmap
    co
    #
    cpw
    #
    @13
    wf
    #
    @2
    cvv
    wcel
    #
    @29
    cvv
    wcel
    #
    @13
    cvv
    wcel
    wph
    @12
    @29
    wcel
    #
    vg
    cB
    wral
    #
    vf
    cB
    wral
    @30
    wph
    @34
    vf
    cB
    wph
    @33
    vg
    cB
    wph
    @12
    @28
    wss
    @33
    wph
    vx
    cI
    @27
    cixp
    #
    @12
    @28
    @11
    @27
    wss
    #
    vx
    cI
    wral
    @12
    @35
    wss
    @36
    vx
    cI
    @11
    @10
    crn
    #
    cuni
    #
    @27
    @10
    @7
    @8
    ovssunirn
    @10
    @25
    wss
    @37
    @26
    wss
    @38
    @27
    wss
    @10
    @9
    crn
    #
    cuni
    #
    @25
    @9
    chom
    cnx
    chom
    cfv
    #
    homid
    strfvss
    @9
    @23
    wss
    @39
    @24
    wss
    @40
    @25
    wss
    cR
    @6
    fvssunirn
    @9
    @23
    rnss
    @39
    @24
    uniss
    mp2b
    sstri
    @10
    @25
    rnss
    @37
    @26
    uniss
    mp2b
    sstri
    rgenw
    vx
    cI
    @11
    @27
    ss2ixp
    ax-mp
    wph
    cI
    cvv
    wcel
    @27
    cvv
    wcel
    #
    @35
    @28
    wceq
    wph
    cR
    cdm
    #
    cI
    cvv
    prdsbas.i
    wph
    cR
    cW
    wcel
    #
    @43
    cvv
    wcel
    prdsbas.r
    cR
    cW
    dmexg
    syl
    eqeltrrd
    wph
    @25
    cvv
    wcel
    #
    @26
    cvv
    wcel
    @42
    wph
    @23
    cvv
    wcel
    #
    @24
    cvv
    wcel
    @45
    wph
    @44
    @22
    cvv
    wcel
    @46
    prdsbas.r
    cR
    cW
    rnexg
    @22
    cvv
    uniexg
    3syl
    @23
    cvv
    rnexg
    @24
    cvv
    uniexg
    3syl
    @25
    cvv
    rnexg
    @26
    cvv
    uniexg
    3syl
    vx
    cI
    @27
    cvv
    cvv
    ixpconstg
    syl2anc
    syl5sseq
    @12
    @28
    @27
    cI
    cmap
    ovex
    #
    elpw2
    sylibr
    ralrimivw
    ralrimivw
    vf
    vg
    cB
    cB
    @12
    @29
    @13
    @13
    eqid
    fmpt2
    sylib
    @31
    wph
    cB
    cB
    cB
    cP
    cbs
    cfv
    cvv
    prdsbas.b
    cP
    cbs
    fvex
    eqeltri
    #
    @48
    xpex
    a1i
    @32
    wph
    @28
    @47
    pwex
    a1i
    @2
    @29
    @13
    cvv
    cvv
    fex2
    syl3anc
    @41
    @13
    cop
    #
    csn
    #
    cnx
    cts
    cfv
    @19
    cop
    cnx
    cple
    cfv
    @18
    cop
    cnx
    cds
    cfv
    @0
    cop
    ctp
    #
    @49
    cnx
    cco
    cfv
    @14
    cop
    #
    cpr
    #
    cun
    #
    cnx
    cbs
    cfv
    cB
    cop
    cnx
    cplusg
    cfv
    @1
    cop
    cnx
    cmulr
    cfv
    @16
    cop
    ctp
    cnx
    csca
    cfv
    cS
    cop
    cnx
    cvsca
    cfv
    @15
    cop
    cnx
    cip
    cfv
    @17
    cop
    ctp
    cun
    #
    @54
    cun
    @50
    @53
    @54
    @49
    @52
    snsspr1
    @53
    @51
    ssun2
    sstri
    @54
    @55
    ssun2
    sstri
    prdsvallem
end
