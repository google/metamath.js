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
include "ctopn.mm"
include "ccom.mm"
include "cpt.mm"
include "cvsca.mm"
include "cmulr.mm"
include "cts.mm"
include "cip.mm"
include "cgsu.mm"
include "cple.mm"
include "cbs.mm"
include "eqid.mm"
include "prdsbas.mm"
include "prdsplusg.mm"
include "prdsmulr.mm"
include "prdsvsca.mm"
include "eqidd.mm"
include "prdsle.mm"
include "prdsds.mm"
include "prdsval.mm"
include "tsetid.mm"
include "fvexd.mm"
include "cnx.mm"
include "csn.mm"
include "ctp.mm"
include "cpr.mm"
include "cun.mm"
include "csca.mm"
include "snsstp1.mm"
include "ssun1.mm"
include "sstri.mm"
include "ssun2.mm"
include "prdsvallem.mm"

theorem prdstset
  let wph: wff ph
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let cI: class I
  let cO: class O
  let cV: class V
  let cW: class W
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
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
  assume prdstset.l: |- O = ( TopSet ` P )


  assert |- ( ph -> O = ( Xt_ ` ( TopOpen o. R ) ) )

  proof
    wph
    cO
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
    @5
    vg
    cv
    cfv
    #
    @5
    cR
    cfv
    #
    chom
    cfv
    co
    cixp
    cmpt2
    #
    co
    @3
    @9
    cfv
    vx
    cI
    @5
    vd
    cv
    cfv
    @5
    ve
    cv
    cfv
    @5
    @3
    c1st
    cfv
    cfv
    @5
    @4
    cfv
    cop
    @5
    @2
    cfv
    @8
    cco
    cfv
    co
    co
    cmpt
    cmpt2
    cmpt2
    #
    ctopn
    cR
    ccom
    #
    cpt
    cfv
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
    cts
    @9
    vf
    vg
    cB
    cB
    cS
    vx
    cI
    @6
    @7
    @8
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
    @12
    wph
    vx
    cB
    @0
    cP
    @1
    cR
    cS
    @10
    @13
    @14
    ve
    vf
    vg
    @9
    @15
    cI
    cS
    cbs
    cfv
    #
    @16
    @12
    cV
    cW
    va
    vc
    vd
    prdsbas.p
    @17
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
    @14
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
    @14
    eqid
    prdsmulr
    wph
    vx
    cB
    cP
    cR
    cS
    @13
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
    @18
    @13
    eqid
    prdsvsca
    wph
    @15
    eqidd
    wph
    @12
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
    @16
    cV
    cW
    prdsbas.p
    prdsbas.s
    prdsbas.r
    prdsbas.b
    prdsbas.i
    @16
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
    @9
    eqidd
    wph
    @10
    eqidd
    prdsbas.s
    prdsbas.r
    prdsval
    prdstset.l
    tsetid
    wph
    @11
    cpt
    fvexd
    cnx
    cts
    cfv
    @12
    cop
    #
    csn
    #
    @19
    cnx
    cple
    cfv
    @16
    cop
    #
    cnx
    cds
    cfv
    @0
    cop
    #
    ctp
    #
    cnx
    chom
    cfv
    @9
    cop
    cnx
    cco
    cfv
    @10
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
    @1
    cop
    cnx
    cmulr
    cfv
    @14
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
    @13
    cop
    cnx
    cip
    cfv
    @15
    cop
    ctp
    cun
    #
    @25
    cun
    @20
    @23
    @25
    @19
    @21
    @22
    snsstp1
    @23
    @24
    ssun1
    sstri
    @25
    @26
    ssun2
    sstri
    prdsvallem
end
