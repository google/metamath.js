include "csca.mm"
include "cfv.mm"
include "cdm.mm"
include "cv.mm"
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
include "scaid.mm"
include "wcel.mm"
include "cvv.mm"
include "elex.mm"
include "syl.mm"
include "cnx.mm"
include "ctp.mm"
include "cts.mm"
include "snsstp1.mm"
include "ssun2.mm"
include "sstri.mm"
include "ssun1.mm"
include "prdsvallem.mm"
include "eqcomd.mm"

theorem prdssca
  let wph: wff ph
  let cP: class P
  let cR: class R
  let cS: class S
  let cV: class V
  let cW: class W
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let cB: class B
  let cH: class H
  let cK: class K
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cI: class I
  assume prdsbas.p: |- P = ( S Xs_ R )
  assume prdsbas.s: |- ( ph -> S e. V )
  assume prdsbas.r: |- ( ph -> R e. W )


  assert |- ( ph -> S = ( Scalar ` P ) )

  proof
    wph
    cP
    csca
    cfv
    #
    cS
    wph
    @0
    vx
    cR
    cdm
    #
    vx
    cv
    #
    cR
    cfv
    #
    cbs
    cfv
    cixp
    #
    vf
    vg
    @4
    @4
    vx
    @1
    @2
    vf
    cv
    #
    cfv
    #
    @2
    vg
    cv
    #
    cfv
    #
    @3
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
    @4
    @4
    vx
    @1
    @6
    @8
    @3
    cplusg
    cfv
    co
    cmpt
    cmpt2
    #
    cS
    va
    vc
    @4
    @4
    cxp
    @4
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
    @4
    @4
    vx
    @1
    @6
    @8
    @3
    chom
    cfv
    co
    cixp
    cmpt2
    #
    co
    @12
    @14
    cfv
    vx
    @1
    @2
    vd
    cv
    cfv
    @2
    ve
    cv
    cfv
    @2
    @12
    c1st
    cfv
    cfv
    @2
    @13
    cfv
    cop
    @2
    @11
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
    cS
    vf
    vg
    cS
    cbs
    cfv
    #
    @4
    vx
    @1
    @5
    @8
    @3
    cvsca
    cfv
    co
    cmpt
    cmpt2
    #
    vf
    vg
    @4
    @4
    vx
    @1
    @6
    @8
    @3
    cmulr
    cfv
    co
    cmpt
    cmpt2
    #
    cP
    csca
    @14
    vf
    vg
    @4
    @4
    cS
    vx
    @1
    @6
    @8
    @3
    cip
    cfv
    co
    cmpt
    cgsu
    co
    cmpt2
    #
    @5
    @7
    cpr
    @4
    wss
    @6
    @8
    @3
    cple
    cfv
    wbr
    vx
    @1
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
    @4
    @9
    cP
    @10
    cR
    cS
    @15
    @17
    @18
    ve
    vf
    vg
    @14
    @19
    @1
    @16
    @20
    @21
    cV
    cW
    va
    vc
    vd
    prdsbas.p
    @16
    eqid
    wph
    @1
    eqidd
    wph
    @4
    eqidd
    wph
    @10
    eqidd
    wph
    @18
    eqidd
    wph
    @17
    eqidd
    wph
    @19
    eqidd
    wph
    @21
    eqidd
    wph
    @20
    eqidd
    wph
    @9
    eqidd
    wph
    @14
    eqidd
    wph
    @15
    eqidd
    prdsbas.s
    prdsbas.r
    prdsval
    @0
    eqid
    scaid
    wph
    cS
    cV
    wcel
    cS
    cvv
    wcel
    prdsbas.s
    cS
    cV
    elex
    syl
    cnx
    csca
    cfv
    cS
    cop
    #
    csn
    #
    cnx
    cbs
    cfv
    @4
    cop
    cnx
    cplusg
    cfv
    @10
    cop
    cnx
    cmulr
    cfv
    @18
    cop
    ctp
    #
    @22
    cnx
    cvsca
    cfv
    @17
    cop
    #
    cnx
    cip
    cfv
    @19
    cop
    #
    ctp
    #
    cun
    #
    @28
    cnx
    cts
    cfv
    @21
    cop
    cnx
    cple
    cfv
    @20
    cop
    cnx
    cds
    cfv
    @9
    cop
    ctp
    cnx
    chom
    cfv
    @14
    cop
    cnx
    cco
    cfv
    @15
    cop
    cpr
    cun
    #
    cun
    @23
    @27
    @28
    @22
    @25
    @26
    snsstp1
    @27
    @24
    ssun2
    sstri
    @28
    @29
    ssun1
    sstri
    prdsvallem
    eqcomd
end
