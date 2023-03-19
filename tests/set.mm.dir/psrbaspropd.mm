include "cvv.mm"
include "wcel.mm"
include "cmps.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "crab.mm"
include "eqid.mm"
include "simpr.mm"
include "psrbas.mm"
include "adantr.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "wn.mm"
include "c0.mm"
include "reldmpsr.mm"
include "ovprc1.mm"
include "fveq2d.mm"
include "adantl.mm"
include "pm2.61dan.mm"

theorem psrbaspropd
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cI: class I
  let va: setvar a
  assume psrbaspropd.e: |- ( ph -> ( Base ` R ) = ( Base ` S ) )


  assert |- ( ph -> ( Base ` ( I mPwSer R ) ) = ( Base ` ( I mPwSer S ) ) )

  proof
    wph
    cI
    cvv
    wcel
    #
    cI
    cR
    cmps
    co
    #
    cbs
    cfv
    #
    cI
    cS
    cmps
    co
    #
    cbs
    cfv
    #
    wceq
    #
    wph
    @0
    wa
    #
    @2
    cR
    cbs
    cfv
    #
    va
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    va
    cn0
    cI
    cmap
    co
    crab
    #
    cmap
    co
    #
    @4
    @6
    @2
    @8
    cR
    @1
    va
    cI
    @7
    cvv
    @1
    eqid
    @7
    eqid
    @8
    eqid
    #
    @2
    eqid
    wph
    @0
    simpr
    #
    psrbas
    @6
    @4
    cS
    cbs
    cfv
    #
    @8
    cmap
    co
    @9
    @6
    @4
    @8
    cS
    @3
    va
    cI
    @12
    cvv
    @3
    eqid
    @12
    eqid
    @10
    @4
    eqid
    @11
    psrbas
    @6
    @7
    @12
    @8
    cmap
    wph
    @7
    @12
    wceq
    @0
    psrbaspropd.e
    adantr
    oveq1d
    eqtr4d
    eqtr4d
    @0
    wn
    #
    @5
    wph
    @13
    @1
    @3
    cbs
    @13
    @1
    c0
    @3
    cI
    cR
    cmps
    reldmpsr
    ovprc1
    cI
    cS
    cmps
    reldmpsr
    ovprc1
    eqtr4d
    fveq2d
    adantl
    pm2.61dan
end
