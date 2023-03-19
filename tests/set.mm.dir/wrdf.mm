include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "cv.mm"
include "cfzo.mm"
include "co.mm"
include "wf.mm"
include "cn0.mm"
include "wrex.mm"
include "chash.mm"
include "cfv.mm"
include "iswrd.mm"
include "wa.mm"
include "simpr.mm"
include "fnfzo0hash.mm"
include "oveq2d.mm"
include "feq2d.mm"
include "mpbird.mm"
include "rexlimiva.mm"
include "sylbi.mm"

theorem wrdf
  let cS: class S
  let cW: class W
  let vl: setvar l
  let cL: class L


  assert |- ( W e. Word S -> W : ( 0 ..^ ( # ` W ) ) --> S )

  proof
    cW
    cS
    cword
    wcel
    cc0
    vl
    cv
    #
    cfzo
    co
    #
    cS
    cW
    wf
    #
    vl
    cn0
    wrex
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    #
    cS
    cW
    wf
    #
    cS
    cW
    vl
    iswrd
    @2
    @5
    vl
    cn0
    @0
    cn0
    wcel
    #
    @2
    wa
    #
    @5
    @2
    @6
    @2
    simpr
    @7
    @4
    @1
    cS
    cW
    @7
    @3
    @0
    cc0
    cfzo
    cS
    cW
    @0
    fnfzo0hash
    oveq2d
    feq2d
    mpbird
    rexlimiva
    sylbi
end
