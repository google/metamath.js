include "wfn.mm"
include "wss.mm"
include "cres.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "wb.mm"
include "wa.mm"
include "fnssres.mm"
include "eqfnfv.mm"
include "wcel.mm"
include "fvres.mm"
include "eqeq12d.mm"
include "ralbiia.mm"
include "syl6bb.mm"
include "syl2an.mm"
include "an4s.mm"

theorem fvreseq0
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G

  disjoint B x
  disjoint F x
  disjoint G x
  assert |- ( ( ( F Fn A /\ G Fn C ) /\ ( B C_ A /\ B C_ C ) ) -> ( ( F |` B ) = ( G |` B ) <-> A. x e. B ( F ` x ) = ( G ` x ) ) )

  proof
    cF
    cA
    wfn
    #
    cB
    cA
    wss
    #
    cG
    cC
    wfn
    #
    cB
    cC
    wss
    #
    cF
    cB
    cres
    #
    cG
    cB
    cres
    #
    wceq
    #
    vx
    cv
    #
    cF
    cfv
    #
    @7
    cG
    cfv
    #
    wceq
    #
    vx
    cB
    wral
    #
    wb
    #
    @0
    @1
    wa
    @4
    cB
    wfn
    #
    @5
    cB
    wfn
    #
    @12
    @2
    @3
    wa
    cA
    cB
    cF
    fnssres
    cC
    cB
    cG
    fnssres
    @13
    @14
    wa
    @6
    @7
    @4
    cfv
    #
    @7
    @5
    cfv
    #
    wceq
    #
    vx
    cB
    wral
    @11
    vx
    cB
    @4
    @5
    eqfnfv
    @17
    @10
    vx
    cB
    @7
    cB
    wcel
    @15
    @8
    @16
    @9
    @7
    cB
    cF
    fvres
    @7
    cB
    cG
    fvres
    eqeq12d
    ralbiia
    syl6bb
    syl2an
    an4s
end
