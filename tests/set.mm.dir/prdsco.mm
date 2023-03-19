include "cds.mm"
include "cfv.mm"
include "cplusg.mm"
include "cxp.mm"
include "cv.mm"
include "c2nd.mm"
include "co.mm"
include "c1st.mm"
include "cop.mm"
include "cco.mm"
include "cmpt.mm"
include "cmpt2.mm"
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
include "prdshom.mm"
include "prdsval.mm"
include "ccoid.mm"
include "cvv.mm"
include "wcel.mm"
include "fvex.mm"
include "eqeltri.mm"
include "xpex.mm"
include "mpt2ex.mm"
include "a1i.mm"
include "cnx.mm"
include "csn.mm"
include "ctp.mm"
include "chom.mm"
include "cpr.mm"
include "cun.mm"
include "csca.mm"
include "snsspr2.mm"
include "ssun2.mm"
include "sstri.mm"
include "prdsvallem.mm"

theorem prdsco
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let c.xb: class .xb
  let ve: setvar e
  let cH: class H
  let cI: class I
  let cV: class V
  let cW: class W
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
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
  assume prdsco.o: |- .xb = ( comp ` P )

  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a x
  disjoint B a
  disjoint c d
  disjoint c e
  disjoint c x
  disjoint B c
  disjoint d e
  disjoint d x
  disjoint B d
  disjoint e x
  disjoint B e
  disjoint B x
  disjoint H a
  disjoint H c
  disjoint H d
  disjoint H e
  disjoint a ph
  disjoint c ph
  disjoint d ph
  disjoint e ph
  disjoint ph x
  disjoint I a
  disjoint I c
  disjoint I d
  disjoint I e
  disjoint I x
  disjoint P x
  disjoint R a
  disjoint R c
  disjoint R d
  disjoint R e
  disjoint R x
  disjoint S a
  disjoint S c
  disjoint S d
  disjoint S e
  disjoint S x
  disjoint a f
  disjoint a g
  disjoint c f
  disjoint c g
  disjoint d f
  disjoint d g
  disjoint e f
  disjoint e g
  disjoint f g
  disjoint f x
  disjoint B f
  disjoint g x
  disjoint B g
  disjoint K f
  disjoint K g
  disjoint f ph
  disjoint g ph
  disjoint a w
  disjoint a y
  disjoint a z
  disjoint c w
  disjoint c y
  disjoint c z
  disjoint d w
  disjoint d y
  disjoint d z
  disjoint e w
  disjoint e y
  disjoint e z
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
  disjoint R f
  disjoint R g
  disjoint R w
  disjoint R y
  disjoint R z
  disjoint S f
  disjoint S g
  assert |- ( ph -> .xb = ( a e. ( B X. B ) , c e. B |-> ( d e. ( c H ( 2nd ` a ) ) , e e. ( H ` a ) |-> ( x e. I |-> ( ( d ` x ) ( <. ( ( 1st ` a ) ` x ) , ( ( 2nd ` a ) ` x ) >. ( comp ` ( R ` x ) ) ( c ` x ) ) ( e ` x ) ) ) ) ) )

  proof
    wph
    c.xb
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
    cH
    co
    @4
    cH
    cfv
    vx
    cI
    vx
    cv
    #
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
    @6
    cR
    cfv
    #
    cco
    cfv
    co
    co
    cmpt
    cmpt2
    #
    cmpt2
    #
    @9
    cP
    cvsca
    cfv
    #
    cP
    cmulr
    cfv
    #
    cP
    cco
    cH
    vf
    vg
    cB
    cB
    cS
    vx
    cI
    @6
    vf
    cv
    cfv
    @6
    vg
    cv
    cfv
    @7
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
    @9
    @10
    @11
    ve
    vf
    vg
    cH
    @12
    cI
    cS
    cbs
    cfv
    #
    @13
    @14
    cV
    cW
    va
    vc
    vd
    prdsbas.p
    @15
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
    @11
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
    @11
    eqid
    prdsmulr
    wph
    vx
    cB
    cP
    cR
    cS
    @10
    vf
    vg
    cI
    @15
    cV
    cW
    prdsbas.p
    prdsbas.s
    prdsbas.r
    prdsbas.b
    prdsbas.i
    @16
    @10
    eqid
    prdsvsca
    wph
    @12
    eqidd
    wph
    cB
    cP
    cR
    cS
    cI
    @14
    cV
    cW
    prdsbas.p
    prdsbas.s
    prdsbas.r
    prdsbas.b
    prdsbas.i
    @14
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
    @13
    cV
    cW
    prdsbas.p
    prdsbas.s
    prdsbas.r
    prdsbas.b
    prdsbas.i
    @13
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
    vx
    cB
    cP
    cR
    cS
    vf
    vg
    cH
    cI
    cV
    cW
    prdsbas.p
    prdsbas.s
    prdsbas.r
    prdsbas.b
    prdsbas.i
    prdshom.h
    prdshom
    wph
    @9
    eqidd
    prdsbas.s
    prdsbas.r
    prdsval
    prdsco.o
    ccoid
    @9
    cvv
    wcel
    wph
    va
    vc
    @2
    cB
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
    @17
    xpex
    @17
    mpt2ex
    a1i
    cnx
    cco
    cfv
    @9
    cop
    #
    csn
    #
    cnx
    cts
    cfv
    @14
    cop
    cnx
    cple
    cfv
    @13
    cop
    cnx
    cds
    cfv
    @0
    cop
    ctp
    #
    cnx
    chom
    cfv
    cH
    cop
    #
    @18
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
    @11
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
    @10
    cop
    cnx
    cip
    cfv
    @12
    cop
    ctp
    cun
    #
    @23
    cun
    @19
    @22
    @23
    @21
    @18
    snsspr2
    @22
    @20
    ssun2
    sstri
    @23
    @24
    ssun2
    sstri
    prdsvallem
end
