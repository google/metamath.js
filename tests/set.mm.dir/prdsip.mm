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
include "cip.mm"
include "cgsu.mm"
include "cbs.mm"
include "cvsca.mm"
include "cmulr.mm"
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
include "ipid.mm"
include "cvv.mm"
include "wcel.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "mpt2exga.mm"
include "sylancl.mm"
include "cnx.mm"
include "ctp.mm"
include "csca.mm"
include "cts.mm"
include "snsstp3.mm"
include "ssun2.mm"
include "sstri.mm"
include "ssun1.mm"
include "prdsvallem.mm"

theorem prdsip
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let vf: setvar f
  let vg: setvar g
  let c.xi: class .,
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
  assume prdsip.m: |- ., = ( .i ` P )

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
  assert |- ( ph -> ., = ( f e. B , g e. B |-> ( S gsum ( x e. I |-> ( ( f ` x ) ( .i ` ( R ` x ) ) ( g ` x ) ) ) ) ) )

  proof
    wph
    c.xi
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
    co
    cmpt
    cmpt2
    #
    cP
    cip
    @11
    @14
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
    @14
    cI
    @15
    @18
    @19
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
    @16
    eqidd
    wph
    @14
    eqidd
    wph
    @19
    eqidd
    wph
    @18
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
    prdsip.m
    ipid
    wph
    cB
    cvv
    wcel
    #
    @20
    @14
    cvv
    wcel
    @20
    wph
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
    a1i
    @21
    vf
    vg
    cB
    cB
    @13
    cvv
    cvv
    mpt2exga
    sylancl
    cnx
    cip
    cfv
    @14
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
    cnx
    cvsca
    cfv
    @16
    cop
    #
    @22
    ctp
    #
    cun
    #
    @28
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
    @23
    @27
    @28
    @25
    @26
    @22
    snsstp3
    @27
    @24
    ssun2
    sstri
    @28
    @29
    ssun1
    sstri
    prdsvallem
end
