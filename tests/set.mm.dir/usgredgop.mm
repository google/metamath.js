include "cusgr.mm"
include "wcel.mm"
include "ciedg.mm"
include "cfv.mm"
include "wceq.mm"
include "wfun.mm"
include "cdm.mm"
include "cpr.mm"
include "cop.mm"
include "wb.mm"
include "usgrfun.mm"
include "funeq.mm"
include "syl5ibrcom.mm"
include "imp.mm"
include "funopfvb.mm"
include "stoic3.mm"

theorem usgredgop
  let cE: class E
  let cG: class G
  let cM: class M
  let cN: class N
  let cX: class X


  assert |- ( ( G e. USGraph /\ E = ( iEdg ` G ) /\ X e. dom E ) -> ( ( E ` X ) = { M , N } <-> <. X , { M , N } >. e. E ) )

  proof
    cG
    cusgr
    wcel
    #
    cE
    cG
    ciedg
    cfv
    #
    wceq
    #
    cE
    wfun
    #
    cX
    cE
    cdm
    wcel
    cX
    cE
    cfv
    cM
    cN
    cpr
    #
    wceq
    cX
    @4
    cop
    cE
    wcel
    wb
    @0
    @2
    @3
    @0
    @3
    @2
    @1
    wfun
    cG
    usgrfun
    cE
    @1
    funeq
    syl5ibrcom
    imp
    cX
    @4
    cE
    funopfvb
    stoic3
end
