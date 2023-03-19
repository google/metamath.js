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
include "cple.mm"
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
include "prdsle.mm"
include "prdsval.mm"
include "dsid.mm"
include "cvv.mm"
include "wcel.mm"
include "cuni.mm"
include "cpw.mm"
include "wf.mm"
include "wral.mm"
include "wbr.mm"
include "wn.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "crab.mm"
include "df-sup.mm"
include "wss.mm"
include "ssrab2.mm"
include "unissi.mm"
include "xrex.mm"
include "uniex.mm"
include "elpw2.mm"
include "mpbir.mm"
include "eqeltri.mm"
include "rgen2w.mm"
include "fmpt2.mm"
include "mpbi.mm"
include "fvex.mm"
include "xpex.mm"
include "pwex.mm"
include "fex2.mm"
include "mp3an.mm"
include "a1i.mm"
include "cnx.mm"
include "cts.mm"
include "ctp.mm"
include "cpr.mm"
include "csca.mm"
include "snsstp3.mm"
include "ssun1.mm"
include "sstri.mm"
include "ssun2.mm"
include "prdsvallem.mm"

theorem prdsds
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
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
  assume prdsds.l: |- D = ( dist ` P )

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
  assert |- ( ph -> D = ( f e. B , g e. B |-> sup ( ( ran ( x e. I |-> ( ( f ` x ) ( dist ` ( R ` x ) ) ( g ` x ) ) ) u. { 0 } ) , RR* , < ) ) )

  proof
    wph
    cD
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
    cfv
    #
    @0
    vg
    cv
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
    #
    cxr
    clt
    csup
    #
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
    @1
    @2
    @3
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
    @3
    cco
    cfv
    co
    co
    cmpt
    cmpt2
    cmpt2
    #
    @6
    cP
    cvsca
    cfv
    #
    cP
    cmulr
    cfv
    #
    cP
    cds
    @12
    vf
    vg
    cB
    cB
    cS
    vx
    cI
    @1
    @2
    @3
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
    @14
    @15
    ve
    vf
    vg
    @12
    @16
    cI
    cS
    cbs
    cfv
    #
    @17
    @18
    cV
    cW
    va
    vc
    vd
    prdsbas.p
    @19
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
    @15
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
    @15
    eqid
    prdsmulr
    wph
    vx
    cB
    cP
    cR
    cS
    @14
    vf
    vg
    cI
    @19
    cV
    cW
    prdsbas.p
    prdsbas.s
    prdsbas.r
    prdsbas.b
    prdsbas.i
    @20
    @14
    eqid
    prdsvsca
    wph
    @16
    eqidd
    wph
    @18
    eqidd
    wph
    vx
    cB
    cP
    cR
    cS
    vf
    vg
    cI
    @17
    cV
    cW
    prdsbas.p
    prdsbas.s
    prdsbas.r
    prdsbas.b
    prdsbas.i
    @17
    eqid
    prdsle
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
    prdsds.l
    dsid
    @6
    cvv
    wcel
    #
    wph
    @8
    cxr
    cuni
    #
    cpw
    #
    @6
    wf
    #
    @8
    cvv
    wcel
    @23
    cvv
    wcel
    @21
    @5
    @23
    wcel
    #
    vg
    cB
    wral
    vf
    cB
    wral
    @24
    @25
    vf
    vg
    cB
    cB
    @5
    vy
    cv
    #
    vz
    cv
    #
    clt
    wbr
    wn
    vz
    @4
    wral
    @27
    @26
    clt
    wbr
    @27
    vw
    cv
    clt
    wbr
    vw
    @4
    wrex
    wi
    vz
    cxr
    wral
    wa
    #
    vy
    cxr
    crab
    #
    cuni
    #
    @23
    vy
    vz
    vw
    @4
    cxr
    clt
    df-sup
    @30
    @23
    wcel
    @30
    @22
    wss
    @29
    cxr
    @28
    vy
    cxr
    ssrab2
    unissi
    @30
    @22
    cxr
    xrex
    uniex
    #
    elpw2
    mpbir
    eqeltri
    rgen2w
    vf
    vg
    cB
    cB
    @5
    @23
    @6
    @6
    eqid
    fmpt2
    mpbi
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
    @32
    xpex
    @22
    @31
    pwex
    @8
    @23
    @6
    cvv
    cvv
    fex2
    mp3an
    a1i
    cnx
    cds
    cfv
    @6
    cop
    #
    csn
    #
    cnx
    cts
    cfv
    @18
    cop
    #
    cnx
    cple
    cfv
    @17
    cop
    #
    @33
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
    @15
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
    @14
    cop
    cnx
    cip
    cfv
    @16
    cop
    ctp
    cun
    #
    @39
    cun
    @34
    @37
    @39
    @35
    @36
    @33
    snsstp3
    @37
    @38
    ssun1
    sstri
    @39
    @40
    ssun2
    sstri
    prdsvallem
end
