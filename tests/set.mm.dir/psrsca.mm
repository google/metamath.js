include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "cplusg.mm"
include "cmulr.mm"
include "ctp.mm"
include "csca.mm"
include "cvsca.mm"
include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "wcel.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "cmpt2.mm"
include "cts.mm"
include "ctopn.mm"
include "cpt.mm"
include "cun.mm"
include "wceq.mm"
include "c1.mm"
include "c9.mm"
include "psrvalstr.mm"
include "scaid.mm"
include "snsstp1.mm"
include "ssun2.mm"
include "sstri.mm"
include "strfv.mm"
include "syl.mm"
include "eqid.mm"
include "psrbas.mm"
include "psrplusg.mm"
include "psrmulr.mm"
include "eqidd.mm"
include "psrval.mm"
include "fveq2d.mm"
include "eqtr4d.mm"

theorem psrsca
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cI: class I
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vh: setvar h
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume psrsca.s: |- S = ( I mPwSer R )
  assume psrsca.i: |- ( ph -> I e. V )
  assume psrsca.r: |- ( ph -> R e. W )


  assert |- ( ph -> R = ( Scalar ` S ) )

  proof
    wph
    cR
    cnx
    cbs
    cfv
    cS
    cbs
    cfv
    #
    cop
    cnx
    cplusg
    cfv
    cS
    cplusg
    cfv
    #
    cop
    cnx
    cmulr
    cfv
    cS
    cmulr
    cfv
    #
    cop
    ctp
    #
    cnx
    csca
    cfv
    cR
    cop
    #
    cnx
    cvsca
    cfv
    vx
    vf
    cR
    cbs
    cfv
    #
    @0
    vh
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vh
    cn0
    cI
    cmap
    co
    crab
    #
    vx
    cv
    csn
    cxp
    vf
    cv
    cR
    cmulr
    cfv
    #
    cof
    co
    cmpt2
    #
    cop
    #
    cnx
    cts
    cfv
    @6
    cR
    ctopn
    cfv
    #
    csn
    cxp
    cpt
    cfv
    #
    cop
    #
    ctp
    #
    cun
    #
    csca
    cfv
    #
    cS
    csca
    cfv
    wph
    cR
    cW
    wcel
    cR
    @15
    wceq
    psrsca.r
    cR
    @14
    csca
    cW
    c1
    c9
    cop
    @0
    @1
    cR
    @8
    @2
    @11
    psrvalstr
    scaid
    @4
    csn
    @13
    @14
    @4
    @9
    @12
    snsstp1
    @13
    @3
    ssun2
    sstri
    strfv
    syl
    wph
    cS
    @14
    csca
    wph
    vx
    vy
    @0
    @6
    cR
    cplusg
    cfv
    #
    @1
    cR
    cS
    @8
    @7
    @2
    vf
    vz
    vh
    vw
    cI
    @11
    @5
    @10
    cV
    cW
    psrsca.s
    @5
    eqid
    #
    @16
    eqid
    #
    @7
    eqid
    #
    @10
    eqid
    @6
    eqid
    #
    wph
    @0
    @6
    cR
    cS
    vh
    cI
    @5
    cV
    psrsca.s
    @17
    @20
    @0
    eqid
    #
    psrsca.i
    psrbas
    @0
    @16
    @1
    cR
    cS
    cI
    psrsca.s
    @21
    @18
    @1
    eqid
    psrplusg
    vx
    vy
    @0
    @6
    cR
    cS
    @2
    @7
    vf
    vz
    vh
    vw
    cI
    psrsca.s
    @21
    @19
    @2
    eqid
    @20
    psrmulr
    @8
    eqid
    wph
    @11
    eqidd
    psrsca.i
    psrsca.r
    psrval
    fveq2d
    eqtr4d
end
