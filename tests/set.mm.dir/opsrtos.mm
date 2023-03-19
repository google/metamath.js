include "cv.mm"
include "cfv.mm"
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
include "cmps.mm"
include "cbs.mm"
include "cple.mm"
include "eqid.mm"
include "biid.mm"
include "opsrtoslem2.mm"

theorem opsrtos
  let wph: wff ph
  let cR: class R
  let cT: class T
  let cI: class I
  let cO: class O
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let vw: setvar w
  let vz: setvar z
  let cC: class C
  let vh: setvar h
  let cD: class D
  let c.lt: class .<
  let wps: wff ps
  assume opsrso.o: |- O = ( ( I ordPwSer R ) ` T )
  assume opsrso.i: |- ( ph -> I e. V )
  assume opsrso.r: |- ( ph -> R e. Toset )
  assume opsrso.t: |- ( ph -> T C_ ( I X. I ) )
  assume opsrso.w: |- ( ph -> T We I )


  assert |- ( ph -> O e. Toset )

  proof
    wph
    vz
    cv
    #
    vx
    cv
    #
    cfv
    @0
    vy
    cv
    #
    cfv
    cR
    cplt
    cfv
    #
    wbr
    vw
    cv
    #
    @0
    cT
    cI
    cltb
    co
    #
    wbr
    @4
    @1
    cfv
    @4
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
    @6
    wrex
    #
    vx
    vy
    vz
    vw
    cI
    cR
    cmps
    co
    #
    cbs
    cfv
    #
    @5
    @6
    cR
    @8
    @3
    cT
    vh
    cI
    cO
    cple
    cfv
    #
    cO
    cV
    opsrso.o
    opsrso.i
    opsrso.r
    opsrso.t
    opsrso.w
    @8
    eqid
    @9
    eqid
    @3
    eqid
    @5
    eqid
    @6
    eqid
    @7
    biid
    @10
    eqid
    opsrtoslem2
end
