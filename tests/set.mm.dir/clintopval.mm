include "wcel.mm"
include "cv.mm"
include "cintop.mm"
include "co.mm"
include "cxp.mm"
include "cmap.mm"
include "cvv.mm"
include "cclintop.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-clintop.mm"
include "a1i.mm"
include "id.mm"
include "oveq12d.mm"
include "intopval.mm"
include "anidms.mm"
include "sylan9eqr.mm"
include "elex.mm"
include "ovexd.mm"
include "fvmptd.mm"

theorem clintopval
  let cM: class M
  let cV: class V
  let vm: setvar m
  let vk: setvar k
  let vx: setvar x


  assert |- ( M e. V -> ( clIntOp ` M ) = ( M ^m ( M X. M ) ) )

  proof
    cM
    cV
    wcel
    #
    vm
    cM
    vm
    cv
    #
    @1
    cintop
    co
    #
    cM
    cM
    cM
    cxp
    #
    cmap
    co
    #
    cvv
    cclintop
    cvv
    cclintop
    vm
    cvv
    @2
    cmpt
    wceq
    @0
    vm
    df-clintop
    a1i
    @1
    cM
    wceq
    #
    @0
    @2
    cM
    cM
    cintop
    co
    #
    @4
    @5
    @1
    cM
    @1
    cM
    cintop
    @5
    id
    #
    @7
    oveq12d
    @0
    @6
    @4
    wceq
    cM
    cM
    cV
    cV
    intopval
    anidms
    sylan9eqr
    cM
    cV
    elex
    @0
    cM
    @3
    cmap
    ovexd
    fvmptd
end
