include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cfa.mm"
include "c1.mm"
include "cfn.mm"
include "wceq.mm"
include "csn.mm"
include "snfi.mm"
include "eqeltri.mm"
include "symghash.mm"
include "ax-mp.mm"
include "fveq2i.mm"
include "hashsng.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "fac1.mm"
include "syl6eq.mm"

theorem symg1hash
  let cA: class A
  let cB: class B
  let cG: class G
  let cI: class I
  let cV: class V
  assume symg1bas.1: |- G = ( SymGrp ` A )
  assume symg1bas.2: |- B = ( Base ` G )
  assume symg1bas.0: |- A = { I }


  assert |- ( I e. V -> ( # ` B ) = 1 )

  proof
    cI
    cV
    wcel
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
    c1
    cA
    cfn
    wcel
    @1
    @3
    wceq
    cA
    cI
    csn
    #
    cfn
    symg1bas.0
    cI
    snfi
    eqeltri
    cA
    cB
    cG
    symg1bas.1
    symg1bas.2
    symghash
    ax-mp
    @0
    @3
    c1
    cfa
    cfv
    c1
    @0
    @2
    c1
    cfa
    @0
    @2
    @4
    chash
    cfv
    c1
    cA
    @4
    chash
    symg1bas.0
    fveq2i
    cI
    cV
    hashsng
    syl5eq
    fveq2d
    fac1
    syl6eq
    syl5eq
end
