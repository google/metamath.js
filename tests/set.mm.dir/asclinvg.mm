include "clmod.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "cghm.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "simp2.mm"
include "simp1.mm"
include "asclghm.mm"
include "simp3.mm"
include "wa.mm"
include "ghminv.mm"
include "eqcomd.mm"
include "syl2anc.mm"

theorem asclinvg
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cI: class I
  let cJ: class J
  let cW: class W
  assume asclinvg.a: |- A = ( algSc ` W )
  assume asclinvg.r: |- R = ( Scalar ` W )
  assume asclinvg.k: |- B = ( Base ` R )
  assume asclinvg.i: |- I = ( invg ` R )
  assume asclinvg.j: |- J = ( invg ` W )


  assert |- ( ( W e. LMod /\ W e. Ring /\ C e. B ) -> ( J ` ( A ` C ) ) = ( A ` ( I ` C ) ) )

  proof
    cW
    clmod
    wcel
    #
    cW
    crg
    wcel
    #
    cC
    cB
    wcel
    #
    w3a
    #
    cA
    cR
    cW
    cghm
    co
    wcel
    #
    @2
    cC
    cA
    cfv
    cJ
    cfv
    #
    cC
    cI
    cfv
    cA
    cfv
    #
    wceq
    @3
    cA
    cR
    cW
    asclinvg.a
    asclinvg.r
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp1
    asclghm
    @0
    @1
    @2
    simp3
    @4
    @2
    wa
    @6
    @5
    cB
    cR
    cW
    cA
    cI
    cJ
    cC
    asclinvg.k
    asclinvg.i
    asclinvg.j
    ghminv
    eqcomd
    syl2anc
end
