include "wf.mm"
include "wa.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "wceq.mm"
include "wf1o.mm"
include "ccnv.mm"
include "simpll.mm"
include "simplr.mm"
include "simprr.mm"
include "simprl.mm"
include "fcof1od.mm"
include "2fcoidinvd.mm"
include "jca.mm"

theorem fcof1o
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G


  assert |- ( ( ( F : A --> B /\ G : B --> A ) /\ ( ( F o. G ) = ( _I |` B ) /\ ( G o. F ) = ( _I |` A ) ) ) -> ( F : A -1-1-onto-> B /\ `' F = G ) )

  proof
    cA
    cB
    cF
    wf
    #
    cB
    cA
    cG
    wf
    #
    wa
    #
    cF
    cG
    ccom
    cid
    cB
    cres
    wceq
    #
    cG
    cF
    ccom
    cid
    cA
    cres
    wceq
    #
    wa
    #
    wa
    #
    cA
    cB
    cF
    wf1o
    cF
    ccnv
    cG
    wceq
    @6
    cA
    cB
    cF
    cG
    @0
    @1
    @5
    simpll
    #
    @0
    @1
    @5
    simplr
    #
    @2
    @3
    @4
    simprr
    #
    @2
    @3
    @4
    simprl
    #
    fcof1od
    @6
    cA
    cB
    cF
    cG
    @7
    @8
    @9
    @10
    2fcoidinvd
    jca
end
