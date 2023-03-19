include "crg.mm"
include "wcel.mm"
include "cfn.mm"
include "clmod.mm"
include "ply1ring.mm"
include "matlmod.mm"
include "sylan2.mm"

theorem pmatlmod
  let cC: class C
  let cP: class P
  let cR: class R
  let cN: class N
  assume pmatring.p: |- P = ( Poly1 ` R )
  assume pmatring.c: |- C = ( N Mat P )


  assert |- ( ( N e. Fin /\ R e. Ring ) -> C e. LMod )

  proof
    cR
    crg
    wcel
    cN
    cfn
    wcel
    cP
    crg
    wcel
    cC
    clmod
    wcel
    cP
    cR
    pmatring.p
    ply1ring
    cC
    cP
    cN
    pmatring.c
    matlmod
    sylan2
end
