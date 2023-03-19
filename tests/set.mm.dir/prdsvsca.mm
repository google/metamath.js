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
include "cvsca.mm"
include "cmulr.mm"
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
include "prdsbas.mm"
include "eqid.mm"
include "prdsplusg.mm"
include "prdsmulr.mm"
include "eqidd.mm"
include "prdsval.mm"
include "vscaid.mm"
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
include "4syl.mm"
include "cdm.mm"
include "dmexg.mm"
include "syl.mm"
include "eqeltrrd.mm"
include "elmapd.mm"
include "mpbird.mm"
include "ralrimivw.mm"
include "fmpt2.mm"
include "sylib.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "xpex.mm"
include "fex2.mm"
include "mp3an23.mm"
include "ctp.mm"
include "csca.mm"
include "cts.mm"
include "snsstp2.mm"
include "ssun2.mm"
include "ssun1.mm"
include "prdsvallem.mm"

theorem prdsvsca
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
  let cK: class K
  let cV: class V
  let cW: class W
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let cH: class H
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume prdsbas.p: |- P = ( S Xs_ R )
  assume prdsbas.s: |- ( ph -> S e. V )
  assume prdsbas.r: |- ( ph -> R e. W )
  assume prdsbas.b: |- B = ( Base ` P )
  assume prdsbas.i: |- ( ph -> dom R = I )
  assume prdsvsca.k: |- K = ( Base ` S )
  assume prdsvsca.m: |- .x. = ( .s ` P )

  disjoint f g
  disjoint f x
  disjoint B f
  disjoint g x
  disjoint B g
  disjoint B x
  disjoint K f
  disjoint K g
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
  assert |- ( ph -> .x. = ( f e. K , g e. B |-> ( x e. I |-> ( f ( .s ` ( R ` x ) ) ( g ` x ) ) ) ) )

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
    @9
    @11
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
    @9
    c1st
    cfv
    cfv
    @0
    @10
    cfv
    cop
    @0
    @8
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
    cK
    cB
    vx
    cI
    @1
    @4
    @5
    cvsca
    cfv
    #
    co
    #
    cmpt
    #
    cmpt2
    #
    @16
    cP
    cmulr
    cfv
    #
    cP
    cvsca
    @11
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
    @12
    @16
    @17
    ve
    vf
    vg
    @11
    @18
    cI
    cK
    @19
    @20
    cV
    cW
    va
    vc
    vd
    prdsbas.p
    prdsvsca.k
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
    vx
    cB
    cP
    cR
    cS
    @17
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
    @17
    eqid
    prdsmulr
    wph
    @16
    eqidd
    wph
    @18
    eqidd
    wph
    @20
    eqidd
    wph
    @19
    eqidd
    wph
    @6
    eqidd
    wph
    @11
    eqidd
    wph
    @12
    eqidd
    prdsbas.s
    prdsbas.r
    prdsval
    prdsvsca.m
    vscaid
    wph
    cK
    cB
    cxp
    #
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
    @16
    wf
    #
    @16
    cvv
    wcel
    #
    wph
    @15
    @29
    wcel
    #
    vg
    cB
    wral
    #
    vf
    cK
    wral
    @30
    wph
    @33
    vf
    cK
    wph
    @32
    vg
    cB
    wph
    @32
    cI
    @28
    @15
    wf
    wph
    vx
    cI
    @14
    @28
    @15
    @14
    @28
    wcel
    #
    wph
    @0
    cI
    wcel
    wa
    @34
    @14
    @27
    wss
    @14
    @13
    crn
    #
    cuni
    #
    @27
    @13
    @1
    @4
    ovssunirn
    @13
    @25
    wss
    @35
    @26
    wss
    @36
    @27
    wss
    @13
    @5
    crn
    #
    cuni
    #
    @25
    @5
    cvsca
    cnx
    cvsca
    cfv
    #
    vscaid
    strfvss
    @5
    @23
    wss
    @37
    @24
    wss
    @38
    @25
    wss
    cR
    @0
    fvssunirn
    @5
    @23
    rnss
    @37
    @24
    uniss
    mp2b
    sstri
    @13
    @25
    rnss
    @35
    @26
    uniss
    mp2b
    sstri
    @14
    @27
    @1
    @4
    @13
    ovex
    elpw
    mpbir
    a1i
    @15
    eqid
    fmptd
    wph
    @28
    cI
    @15
    cvv
    cvv
    wph
    @25
    cvv
    wcel
    #
    @26
    cvv
    wcel
    @27
    cvv
    wcel
    @28
    cvv
    wcel
    wph
    @23
    cvv
    wcel
    #
    @24
    cvv
    wcel
    @40
    wph
    cR
    cW
    wcel
    #
    @22
    cvv
    wcel
    @41
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
    @27
    cvv
    pwexg
    4syl
    wph
    cR
    cdm
    #
    cI
    cvv
    prdsbas.i
    wph
    @42
    @43
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
    cK
    cB
    @15
    @29
    @16
    @16
    eqid
    fmpt2
    sylib
    @30
    @21
    cvv
    wcel
    @29
    cvv
    wcel
    @31
    cK
    cB
    cK
    cS
    cbs
    cfv
    cvv
    prdsvsca.k
    cS
    cbs
    fvex
    eqeltri
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
    xpex
    @28
    cI
    cmap
    ovex
    @21
    @29
    @16
    cvv
    cvv
    fex2
    mp3an23
    syl
    @39
    @16
    cop
    #
    csn
    #
    cnx
    cbs
    cfv
    cB
    cop
    cnx
    cplusg
    cfv
    @7
    cop
    cnx
    cmulr
    cfv
    @17
    cop
    ctp
    #
    cnx
    csca
    cfv
    cS
    cop
    #
    @44
    cnx
    cip
    cfv
    @18
    cop
    #
    ctp
    #
    cun
    #
    @50
    cnx
    cts
    cfv
    @20
    cop
    cnx
    cple
    cfv
    @19
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
    @11
    cop
    cnx
    cco
    cfv
    @12
    cop
    cpr
    cun
    #
    cun
    @45
    @49
    @50
    @47
    @44
    @48
    snsstp2
    @49
    @46
    ssun2
    sstri
    @50
    @51
    ssun1
    sstri
    prdsvallem
end
