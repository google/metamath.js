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
include "cpr.mm"
include "wss.mm"
include "cple.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "copab.mm"
include "cvsca.mm"
include "cmulr.mm"
include "cip.mm"
include "cgsu.mm"
include "ctopn.mm"
include "ccom.mm"
include "cpt.mm"
include "cbs.mm"
include "eqid.mm"
include "prdsbas.mm"
include "prdsplusg.mm"
include "prdsmulr.mm"
include "prdsvsca.mm"
include "eqidd.mm"
include "prdsval.mm"
include "pleid.mm"
include "cvv.mm"
include "wcel.mm"
include "fvex.mm"
include "eqeltri.mm"
include "xpex.mm"
include "vex.mm"
include "prss.mm"
include "anbi1i.mm"
include "opabbii.mm"
include "opabssxp.mm"
include "eqsstr3i.mm"
include "ssexi.mm"
include "a1i.mm"
include "cnx.mm"
include "cts.mm"
include "ctp.mm"
include "csca.mm"
include "snsstp2.mm"
include "ssun1.mm"
include "sstri.mm"
include "ssun2.mm"
include "prdsvallem.mm"

theorem prdsle
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let vf: setvar f
  let vg: setvar g
  let cI: class I
  let c.le: class .<_
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
  assume prdsle.l: |- .<_ = ( le ` P )

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
  assert |- ( ph -> .<_ = { <. f , g >. | ( { f , g } C_ B /\ A. x e. I ( f ` x ) ( le ` ( R ` x ) ) ( g ` x ) ) } )

  proof
    wph
    c.le
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
    @1
    @3
    cpr
    cB
    wss
    #
    @2
    @4
    @5
    cple
    cfv
    wbr
    vx
    cI
    wral
    #
    wa
    #
    vf
    vg
    copab
    #
    cP
    cvsca
    cfv
    #
    cP
    cmulr
    cfv
    #
    cP
    cple
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
    @17
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
    @18
    @19
    ve
    vf
    vg
    @12
    @20
    cI
    cS
    cbs
    cfv
    #
    @17
    @21
    cV
    cW
    va
    vc
    vd
    prdsbas.p
    @22
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
    @19
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
    @19
    eqid
    prdsmulr
    wph
    vx
    cB
    cP
    cR
    cS
    @18
    vf
    vg
    cI
    @22
    cV
    cW
    prdsbas.p
    prdsbas.s
    prdsbas.r
    prdsbas.b
    prdsbas.i
    @23
    @18
    eqid
    prdsvsca
    wph
    @20
    eqidd
    wph
    @21
    eqidd
    wph
    @17
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
    prdsle.l
    pleid
    @17
    cvv
    wcel
    wph
    @17
    @8
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
    @24
    xpex
    @17
    @1
    cB
    wcel
    @3
    cB
    wcel
    wa
    #
    @15
    wa
    #
    vf
    vg
    copab
    @8
    @26
    @16
    vf
    vg
    @25
    @14
    @15
    @1
    @3
    cB
    vf
    vex
    vg
    vex
    prss
    anbi1i
    opabbii
    @15
    vf
    vg
    cB
    cB
    opabssxp
    eqsstr3i
    ssexi
    a1i
    cnx
    cple
    cfv
    @17
    cop
    #
    csn
    #
    cnx
    cts
    cfv
    @21
    cop
    #
    @27
    cnx
    cds
    cfv
    @6
    cop
    #
    ctp
    #
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
    @7
    cop
    cnx
    cmulr
    cfv
    @19
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
    @18
    cop
    cnx
    cip
    cfv
    @20
    cop
    ctp
    cun
    #
    @33
    cun
    @28
    @31
    @33
    @29
    @27
    @30
    snsstp2
    @31
    @32
    ssun1
    sstri
    @33
    @34
    ssun2
    sstri
    prdsvallem
end
