include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "cmap.mm"
include "co.mm"
include "cfrlm.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "xpfi.mm"
include "anidms.mm"
include "anim2i.mm"
include "ancoms.mm"
include "eqid.mm"
include "frlmfibas.mm"
include "syl.mm"
include "matbas.mm"
include "eqtrd.mm"

theorem matbas2
  let cA: class A
  let cR: class R
  let cK: class K
  let cN: class N
  let cV: class V
  assume matbas2.a: |- A = ( N Mat R )
  assume matbas2.k: |- K = ( Base ` R )


  assert |- ( ( N e. Fin /\ R e. V ) -> ( K ^m ( N X. N ) ) = ( Base ` A ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    cV
    wcel
    #
    wa
    #
    cK
    cN
    cN
    cxp
    #
    cmap
    co
    #
    cR
    @3
    cfrlm
    co
    #
    cbs
    cfv
    #
    cA
    cbs
    cfv
    @2
    @1
    @3
    cfn
    wcel
    #
    wa
    #
    @4
    @6
    wceq
    @1
    @0
    @8
    @0
    @7
    @1
    @0
    @7
    cN
    cN
    xpfi
    anidms
    anim2i
    ancoms
    cR
    @5
    @3
    cK
    cV
    @5
    eqid
    #
    matbas2.k
    frlmfibas
    syl
    cA
    cR
    @5
    cN
    cV
    matbas2.a
    @9
    matbas
    eqtrd
end
