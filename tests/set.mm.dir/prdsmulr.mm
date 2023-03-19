include "cv.mm"
include "cfv.mm"
include "cds.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "cc0.mm"
include "csn.mm"
include "cun.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cmpt2.mm"
include "cplusg.mm"
include "cxp.mm"
include "c2nd.mm"
include "chom.mm"
include "cixp.mm"
include "c1st.mm"
include "cop.mm"
include "cco.mm"
include "cmulr.mm"
include "cbs.mm"
include "cvsca.mm"
include "cip.mm"
include "cgsu.mm"
include "cpr.mm"
include "wss.mm"
include "cple.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "copab.mm"
include "ctopn.mm"
include "ccom.mm"
include "cpt.mm"
include "eqid.mm"
include "prdsbas.mm"
include "prdsplusg.mm"
include "eqidd.mm"
include "prdsval.mm"
include "mulrid.mm"
include "cuni.mm"
include "cpw.mm"
include "cmap.mm"
include "wf.mm"
include "cvv.mm"
include "wcel.mm"
include "ovssunirn.mm"
include "cnx.mm"
include "strfvss.mm"
include "fvssunirn.mm"
include "rnss.mm"
include "uniss.mm"
include "mp2b.mm"
include "sstri.mm"
include "ovex.mm"
include "elpw.mm"
include "mpbir.mm"
include "a1i.mm"
include "fmptd.mm"
include "rnexg.mm"
include "uniexg.mm"
include "3syl.mm"
include "pwexg.mm"
include "syl.mm"
include "cdm.mm"
include "dmexg.mm"
include "eqeltrrd.mm"
include "elmapd.mm"
include "mpbird.mm"
include "ralrimivw.mm"
include "fmpt2.mm"
include "sylib.mm"
include "fvex.mm"
include "eqeltri.mm"
include "xpex.mm"
include "fex2.mm"
include "mp3an23.mm"
include "ctp.mm"
include "csca.mm"
include "cts.mm"
include "snsstp3.mm"
include "ssun1.mm"
include "prdsvallem.mm"

theorem prdsmulr
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let vf: setvar f
  let vg: setvar g
  let cI: class I
  let cV: class V
  let cW: class W
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let cH: class H
  let cK: class K
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume prdsbas.p: |- P = ( S Xs_ R )
  assume prdsbas.s: |- ( ph -> S e. V )
  assume prdsbas.r: |- ( ph -> R e. W )
  assume prdsbas.b: |- B = ( Base ` P )
  assume prdsbas.i: |- ( ph -> dom R = I )
  assume prdsmulr.t: |- .x. = ( .r ` P )

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
  assert |- ( ph -> .x. = ( f e. B , g e. B |-> ( x e. I |-> ( ( f ` x ) ( .r ` ( R ` x ) ) ( g ` x ) ) ) ) )

  proof
    wph
    c.x
    cB
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
    #
    cfv
    #
    @0
    vg
    cv
    #
    cfv
    #
    @0
    cR
    cfv
    #
    cds
    cfv
    co
    cmpt
    crn
    cc0
    csn
    cun
    cxr
    clt
    csup
    cmpt2
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
    @2
    @4
    @5
    chom
    cfv
    co
    cixp
    cmpt2
    #
    co
    @10
    @12
    cfv
    vx
    cI
    @0
    vd
    cv
    cfv
    @0
    ve
    cv
    cfv
    @0
    @10
    c1st
    cfv
    cfv
    @0
    @11
    cfv
    cop
    @0
    @9
    cfv
    @5
    cco
    cfv
    co
    co
    cmpt
    cmpt2
    cmpt2
    #
    vf
    vg
    cB
    cB
    vx
    cI
    @2
    @4
    @5
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    cmpt2
    #
    vf
    vg
    cS
    cbs
    cfv
    #
    cB
    vx
    cI
    @1
    @4
    @5
    cvsca
    cfv
    co
    cmpt
    cmpt2
    #
    @17
    cP
    cmulr
    @12
    vf
    vg
    cB
    cB
    cS
    vx
    cI
    @2
    @4
    @5
    cip
    cfv
    co
    cmpt
    cgsu
    co
    cmpt2
    #
    @1
    @3
    cpr
    cB
    wss
    @2
    @4
    @5
    cple
    cfv
    wbr
    vx
    cI
    wral
    wa
    vf
    vg
    copab
    #
    ctopn
    cR
    ccom
    cpt
    cfv
    #
    wph
    vx
    cB
    @6
    cP
    @7
    cR
    cS
    @13
    @19
    @17
    ve
    vf
    vg
    @12
    @20
    cI
    @18
    @21
    @22
    cV
    cW
    va
    vc
    vd
    prdsbas.p
    @18
    eqid
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
    @7
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
    @7
    eqid
    prdsplusg
    wph
    @17
    eqidd
    wph
    @19
    eqidd
    wph
    @20
    eqidd
    wph
    @22
    eqidd
    wph
    @21
    eqidd
    wph
    @6
    eqidd
    wph
    @12
    eqidd
    wph
    @13
    eqidd
    prdsbas.s
    prdsbas.r
    prdsval
    prdsmulr.t
    mulrid
    wph
    @8
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
    cpw
    #
    cI
    cmap
    co
    #
    @17
    wf
    #
    @17
    cvv
    wcel
    #
    wph
    @16
    @30
    wcel
    #
    vg
    cB
    wral
    #
    vf
    cB
    wral
    @31
    wph
    @34
    vf
    cB
    wph
    @33
    vg
    cB
    wph
    @33
    cI
    @29
    @16
    wf
    wph
    vx
    cI
    @15
    @29
    @16
    @15
    @29
    wcel
    #
    wph
    @0
    cI
    wcel
    wa
    @35
    @15
    @28
    wss
    @15
    @14
    crn
    #
    cuni
    #
    @28
    @14
    @2
    @4
    ovssunirn
    @14
    @26
    wss
    @36
    @27
    wss
    @37
    @28
    wss
    @14
    @5
    crn
    #
    cuni
    #
    @26
    @5
    cmulr
    cnx
    cmulr
    cfv
    #
    mulrid
    strfvss
    @5
    @24
    wss
    @38
    @25
    wss
    @39
    @26
    wss
    cR
    @0
    fvssunirn
    @5
    @24
    rnss
    @38
    @25
    uniss
    mp2b
    sstri
    @14
    @26
    rnss
    @36
    @27
    uniss
    mp2b
    sstri
    @15
    @28
    @2
    @4
    @14
    ovex
    elpw
    mpbir
    a1i
    @16
    eqid
    fmptd
    wph
    @29
    cI
    @16
    cvv
    cvv
    wph
    @28
    cvv
    wcel
    #
    @29
    cvv
    wcel
    wph
    @26
    cvv
    wcel
    #
    @27
    cvv
    wcel
    @41
    wph
    @24
    cvv
    wcel
    #
    @25
    cvv
    wcel
    @42
    wph
    cR
    cW
    wcel
    #
    @23
    cvv
    wcel
    @43
    prdsbas.r
    cR
    cW
    rnexg
    @23
    cvv
    uniexg
    3syl
    @24
    cvv
    rnexg
    @25
    cvv
    uniexg
    3syl
    @26
    cvv
    rnexg
    @27
    cvv
    uniexg
    3syl
    @28
    cvv
    pwexg
    syl
    wph
    cR
    cdm
    #
    cI
    cvv
    prdsbas.i
    wph
    @44
    @45
    cvv
    wcel
    prdsbas.r
    cR
    cW
    dmexg
    syl
    eqeltrrd
    elmapd
    mpbird
    ralrimivw
    ralrimivw
    vf
    vg
    cB
    cB
    @16
    @30
    @17
    @17
    eqid
    fmpt2
    sylib
    @31
    @8
    cvv
    wcel
    @30
    cvv
    wcel
    @32
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
    @46
    xpex
    @29
    cI
    cmap
    ovex
    @8
    @30
    @17
    cvv
    cvv
    fex2
    mp3an23
    syl
    @40
    @17
    cop
    #
    csn
    #
    cnx
    cbs
    cfv
    cB
    cop
    #
    cnx
    cplusg
    cfv
    @7
    cop
    #
    @47
    ctp
    #
    cnx
    csca
    cfv
    cS
    cop
    cnx
    cvsca
    cfv
    @19
    cop
    cnx
    cip
    cfv
    @20
    cop
    ctp
    #
    cun
    #
    @53
    cnx
    cts
    cfv
    @22
    cop
    cnx
    cple
    cfv
    @21
    cop
    cnx
    cds
    cfv
    @6
    cop
    ctp
    cnx
    chom
    cfv
    @12
    cop
    cnx
    cco
    cfv
    @13
    cop
    cpr
    cun
    #
    cun
    @48
    @51
    @53
    @49
    @50
    @47
    snsstp3
    @51
    @52
    ssun1
    sstri
    @53
    @54
    ssun1
    sstri
    prdsvallem
end
