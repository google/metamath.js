include "clmod.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cpw.mm"
include "cv.mm"
include "wss.mm"
include "crab.mm"
include "cint.mm"
include "cmpt.mm"
include "eqid.mm"
include "lspfval.mm"
include "cmre.mm"
include "wceq.mm"
include "lssmre.mm"
include "mrcfval.mm"
include "syl.mm"
include "eqtr4d.mm"

theorem mrclsp
  let cU: class U
  let cF: class F
  let cK: class K
  let cW: class W
  let va: setvar a
  let vb: setvar b
  assume mrclsp.u: |- U = ( LSubSp ` W )
  assume mrclsp.k: |- K = ( LSpan ` W )
  assume mrclsp.f: |- F = ( mrCls ` U )


  assert |- ( W e. LMod -> K = F )

  proof
    cW
    clmod
    wcel
    #
    cK
    va
    cW
    cbs
    cfv
    #
    cpw
    va
    cv
    vb
    cv
    wss
    vb
    cU
    crab
    cint
    cmpt
    #
    cF
    vb
    cU
    cK
    @1
    cW
    clmod
    va
    @1
    eqid
    #
    mrclsp.u
    mrclsp.k
    lspfval
    @0
    cU
    @1
    cmre
    cfv
    wcel
    cF
    @2
    wceq
    @1
    cU
    cW
    @3
    mrclsp.u
    lssmre
    va
    cU
    cF
    @1
    vb
    mrclsp.f
    mrcfval
    syl
    eqtr4d
end
