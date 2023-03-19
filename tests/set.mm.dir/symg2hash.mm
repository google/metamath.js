include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "chash.mm"
include "cfv.mm"
include "cfa.mm"
include "c2.mm"
include "cfn.mm"
include "wceq.mm"
include "cpr.mm"
include "prfi.mm"
include "eqeltri.mm"
include "symghash.mm"
include "ax-mp.mm"
include "fveq2i.mm"
include "cvv.mm"
include "elex.mm"
include "id.mm"
include "3anim123i.mm"
include "hashprb.mm"
include "sylib.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "fac2.mm"
include "syl6eq.mm"

theorem symg2hash
  let cA: class A
  let cB: class B
  let cG: class G
  let cI: class I
  let cJ: class J
  let cV: class V
  let cW: class W
  assume symg1bas.1: |- G = ( SymGrp ` A )
  assume symg1bas.2: |- B = ( Base ` G )
  assume symg2bas.0: |- A = { I , J }


  assert |- ( ( I e. V /\ J e. W /\ I =/= J ) -> ( # ` B ) = 2 )

  proof
    cI
    cV
    wcel
    #
    cJ
    cW
    wcel
    #
    cI
    cJ
    wne
    #
    w3a
    #
    cB
    chash
    cfv
    #
    cA
    chash
    cfv
    #
    cfa
    cfv
    #
    c2
    cA
    cfn
    wcel
    @4
    @6
    wceq
    cA
    cI
    cJ
    cpr
    #
    cfn
    symg2bas.0
    cI
    cJ
    prfi
    eqeltri
    cA
    cB
    cG
    symg1bas.1
    symg1bas.2
    symghash
    ax-mp
    @3
    @6
    c2
    cfa
    cfv
    c2
    @3
    @5
    c2
    cfa
    @3
    @5
    @7
    chash
    cfv
    #
    c2
    cA
    @7
    chash
    symg2bas.0
    fveq2i
    @3
    cI
    cvv
    wcel
    #
    cJ
    cvv
    wcel
    #
    @2
    w3a
    @8
    c2
    wceq
    @0
    @9
    @1
    @10
    @2
    @2
    cI
    cV
    elex
    cJ
    cW
    elex
    @2
    id
    3anim123i
    cI
    cJ
    hashprb
    sylib
    syl5eq
    fveq2d
    fac2
    syl6eq
    syl5eq
end
