include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cxp.mm"
include "cmap.mm"
include "co.mm"
include "id.mm"
include "syl6eleq.mm"
include "cfn.mm"
include "cvv.mm"
include "wa.mm"
include "wceq.mm"
include "matrcl.mm"
include "matbas2.mm"
include "syl.mm"
include "eleqtrrd.mm"

theorem matbas2i
  let cA: class A
  let cB: class B
  let cR: class R
  let cK: class K
  let cM: class M
  let cN: class N
  assume matbas2.a: |- A = ( N Mat R )
  assume matbas2.k: |- K = ( Base ` R )
  assume matbas2i.b: |- B = ( Base ` A )


  assert |- ( M e. B -> M e. ( K ^m ( N X. N ) ) )

  proof
    cM
    cB
    wcel
    #
    cM
    cA
    cbs
    cfv
    #
    cK
    cN
    cN
    cxp
    cmap
    co
    #
    @0
    cM
    cB
    @1
    @0
    id
    matbas2i.b
    syl6eleq
    @0
    cN
    cfn
    wcel
    cR
    cvv
    wcel
    wa
    @2
    @1
    wceq
    cA
    cB
    cR
    cN
    cM
    matbas2.a
    matbas2i.b
    matrcl
    cA
    cR
    cK
    cN
    cvv
    matbas2.a
    matbas2.k
    matbas2
    syl
    eleqtrrd
end
