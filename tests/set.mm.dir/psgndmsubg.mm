include "wcel.mm"
include "cdm.mm"
include "cv.mm"
include "cid.mm"
include "cdif.mm"
include "cfn.mm"
include "cbs.mm"
include "cfv.mm"
include "crab.mm"
include "csubg.mm"
include "wfn.mm"
include "wceq.mm"
include "eqid.mm"
include "psgnfn.mm"
include "fndm.mm"
include "ax-mp.mm"
include "symgfisg.mm"
include "syl5eqel.mm"

theorem psgndmsubg
  let cD: class D
  let cG: class G
  let cN: class N
  let cV: class V
  let cB: class B
  let vp: setvar p
  let cP: class P
  assume psgneldm.g: |- G = ( SymGrp ` D )
  assume psgneldm.n: |- N = ( pmSgn ` D )


  assert |- ( D e. V -> dom N e. ( SubGrp ` G ) )

  proof
    cD
    cV
    wcel
    cN
    cdm
    #
    vp
    cv
    cid
    cdif
    cdm
    cfn
    wcel
    vp
    cG
    cbs
    cfv
    #
    crab
    #
    cG
    csubg
    cfv
    cN
    @2
    wfn
    @0
    @2
    wceq
    @1
    cD
    @2
    cG
    cN
    vp
    psgneldm.g
    @1
    eqid
    #
    @2
    eqid
    psgneldm.n
    psgnfn
    @2
    cN
    fndm
    ax-mp
    vp
    @1
    cD
    cG
    cV
    psgneldm.g
    @3
    symgfisg
    syl5eqel
end
