include "cnx.mm"
include "cple.mm"
include "cfv.mm"
include "cv.mm"
include "cpr.mm"
include "cbs.mm"
include "wss.mm"
include "cplt.mm"
include "wbr.mm"
include "cltb.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "wcel.mm"
include "cn0.mm"
include "cmap.mm"
include "crab.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "wo.mm"
include "copab.mm"
include "cop.mm"
include "csts.mm"
include "eqid.mm"
include "opsrval.mm"
include "opsrle.mm"
include "opeq2d.mm"
include "oveq2d.mm"
include "eqtr4d.mm"

theorem opsrval2
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cT: class T
  let cI: class I
  let c.le: class .<_
  let cO: class O
  let cV: class V
  let cW: class W
  let vh: setvar h
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume opsrval2.s: |- S = ( I mPwSer R )
  assume opsrval2.o: |- O = ( ( I ordPwSer R ) ` T )
  assume opsrval2.l: |- .<_ = ( le ` O )
  assume opsrval2.i: |- ( ph -> I e. V )
  assume opsrval2.r: |- ( ph -> R e. W )
  assume opsrval2.t: |- ( ph -> T C_ ( I X. I ) )


  assert |- ( ph -> O = ( S sSet <. ( le ` ndx ) , .<_ >. ) )

  proof
    wph
    cO
    cS
    cnx
    cple
    cfv
    #
    vx
    cv
    #
    vy
    cv
    #
    cpr
    cS
    cbs
    cfv
    #
    wss
    vz
    cv
    #
    @1
    cfv
    @4
    @2
    cfv
    cR
    cplt
    cfv
    #
    wbr
    vw
    cv
    #
    @4
    cT
    cI
    cltb
    co
    #
    wbr
    @6
    @1
    cfv
    @6
    @2
    cfv
    wceq
    wi
    vw
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
    wral
    wa
    vz
    @8
    wrex
    @1
    @2
    wceq
    wo
    wa
    vx
    vy
    copab
    #
    cop
    #
    csts
    co
    cS
    @0
    c.le
    cop
    #
    csts
    co
    wph
    vx
    vy
    vz
    vw
    @3
    @7
    @8
    cR
    cS
    @5
    cT
    vh
    cI
    @9
    cO
    cV
    cW
    opsrval2.s
    opsrval2.o
    @3
    eqid
    #
    @5
    eqid
    #
    @7
    eqid
    #
    @8
    eqid
    #
    @9
    eqid
    opsrval2.i
    opsrval2.r
    opsrval2.t
    opsrval
    wph
    @11
    @10
    cS
    csts
    wph
    c.le
    @9
    @0
    wph
    vx
    vy
    vz
    vw
    @3
    @7
    @8
    cR
    cS
    @5
    cT
    vh
    cI
    c.le
    cO
    opsrval2.s
    opsrval2.o
    @12
    @13
    @14
    @15
    opsrval2.l
    opsrval2.t
    opsrle
    opeq2d
    oveq2d
    eqtr4d
end
