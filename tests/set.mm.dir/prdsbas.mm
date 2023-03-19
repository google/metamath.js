include "cv.mm"
include "cfv.mm"
include "cbs.mm"
include "cixp.mm"
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
include "eqid.mm"
include "eqidd.mm"
include "prdsval.mm"
include "baseid.mm"
include "ciun.mm"
include "cvv.mm"
include "wcel.mm"
include "cmap.mm"
include "cuni.mm"
include "cnx.mm"
include "strfvss.mm"
include "fvssunirn.mm"
include "rnss.mm"
include "uniss.mm"
include "mp2b.mm"
include "sstri.mm"
include "rgenw.mm"
include "iunss.mm"
include "mpbir.mm"
include "rnexg.mm"
include "uniexg.mm"
include "3syl.mm"
include "ssexg.mm"
include "sylancr.mm"
include "ixpssmap2g.mm"
include "ovex.mm"
include "ssex.mm"
include "ctp.mm"
include "csca.mm"
include "cts.mm"
include "snsstp1.mm"
include "ssun1.mm"
include "prdsvallem.mm"

theorem prdsbas
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let cI: class I
  let cV: class V
  let cW: class W
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
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

  disjoint B x
  disjoint ph x
  disjoint I x
  disjoint P x
  disjoint R x
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
  disjoint f g
  disjoint f x
  disjoint B f
  disjoint g x
  disjoint B g
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
  disjoint f ph
  disjoint g ph
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
  disjoint I f
  disjoint g w
  disjoint g y
  disjoint g z
  disjoint I g
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint I w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint I y
  disjoint I z
  disjoint P f
  disjoint P g
  disjoint R a
  disjoint R c
  disjoint R d
  disjoint R e
  disjoint R f
  disjoint R g
  disjoint R w
  disjoint R y
  disjoint R z
  disjoint S a
  disjoint S c
  disjoint S d
  disjoint S e
  disjoint S f
  disjoint S g
  assert |- ( ph -> B = X_ x e. I ( Base ` ( R ` x ) ) )

  proof
    wph
    cB
    vx
    cI
    vx
    cv
    #
    cR
    cfv
    #
    cbs
    cfv
    #
    cixp
    #
    vf
    vg
    @3
    @3
    vx
    cI
    @0
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
    @1
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
    vf
    vg
    @3
    @3
    vx
    cI
    @5
    @7
    @1
    cplusg
    cfv
    co
    cmpt
    cmpt2
    #
    cS
    va
    vc
    @3
    @3
    cxp
    @3
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
    @3
    @3
    vx
    cI
    @5
    @7
    @1
    chom
    cfv
    co
    cixp
    cmpt2
    #
    co
    @11
    @13
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
    @11
    c1st
    cfv
    cfv
    @0
    @12
    cfv
    cop
    @0
    @10
    cfv
    @1
    cco
    cfv
    co
    co
    cmpt
    cmpt2
    cmpt2
    #
    @3
    vf
    vg
    cS
    cbs
    cfv
    #
    @3
    vx
    cI
    @4
    @7
    @1
    cvsca
    cfv
    co
    cmpt
    cmpt2
    #
    vf
    vg
    @3
    @3
    vx
    cI
    @5
    @7
    @1
    cmulr
    cfv
    co
    cmpt
    cmpt2
    #
    cP
    cbs
    @13
    vf
    vg
    @3
    @3
    cS
    vx
    cI
    @5
    @7
    @1
    cip
    cfv
    co
    cmpt
    cgsu
    co
    cmpt2
    #
    @4
    @6
    cpr
    @3
    wss
    @5
    @7
    @1
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
    @3
    @8
    cP
    @9
    cR
    cS
    @14
    @16
    @17
    ve
    vf
    vg
    @13
    @18
    cI
    @15
    @19
    @20
    cV
    cW
    va
    vc
    vd
    prdsbas.p
    @15
    eqid
    prdsbas.i
    wph
    @3
    eqidd
    wph
    @9
    eqidd
    wph
    @17
    eqidd
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
    @8
    eqidd
    wph
    @13
    eqidd
    wph
    @14
    eqidd
    prdsbas.s
    prdsbas.r
    prdsval
    prdsbas.b
    baseid
    wph
    vx
    cI
    @2
    ciun
    #
    cvv
    wcel
    #
    @3
    @21
    cI
    cmap
    co
    #
    wss
    @3
    cvv
    wcel
    wph
    @21
    cR
    crn
    #
    cuni
    #
    crn
    #
    cuni
    #
    wss
    #
    @27
    cvv
    wcel
    #
    @22
    @28
    @2
    @27
    wss
    #
    vx
    cI
    wral
    @30
    vx
    cI
    @2
    @1
    crn
    #
    cuni
    #
    @27
    @1
    cbs
    cnx
    cbs
    cfv
    #
    baseid
    strfvss
    @1
    @25
    wss
    @31
    @26
    wss
    @32
    @27
    wss
    cR
    @0
    fvssunirn
    @1
    @25
    rnss
    @31
    @26
    uniss
    mp2b
    sstri
    rgenw
    vx
    cI
    @2
    @27
    iunss
    mpbir
    wph
    @25
    cvv
    wcel
    #
    @26
    cvv
    wcel
    @29
    wph
    cR
    cW
    wcel
    @24
    cvv
    wcel
    @34
    prdsbas.r
    cR
    cW
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
    @21
    @27
    cvv
    ssexg
    sylancr
    vx
    cI
    @2
    cvv
    ixpssmap2g
    @3
    @23
    @21
    cI
    cmap
    ovex
    ssex
    3syl
    @33
    @3
    cop
    #
    csn
    #
    @35
    cnx
    cplusg
    cfv
    @9
    cop
    #
    cnx
    cmulr
    cfv
    @17
    cop
    #
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
    @16
    cop
    cnx
    cip
    cfv
    @18
    cop
    ctp
    #
    cun
    #
    @41
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
    @8
    cop
    ctp
    cnx
    chom
    cfv
    @13
    cop
    cnx
    cco
    cfv
    @14
    cop
    cpr
    cun
    #
    cun
    @36
    @39
    @41
    @35
    @37
    @38
    snsstp1
    @39
    @40
    ssun1
    sstri
    @41
    @42
    ssun1
    sstri
    prdsvallem
end
