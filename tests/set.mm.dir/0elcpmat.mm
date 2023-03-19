include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "csubg.mm"
include "cfv.mm"
include "c0g.mm"
include "cpmatsubgpmat.mm"
include "eqid.mm"
include "subg0cl.mm"
include "syl.mm"

theorem 0elcpmat
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let cN: class N
  assume 0elcpmat.s: |- S = ( N ConstPolyMat R )
  assume 0elcpmat.p: |- P = ( Poly1 ` R )
  assume 0elcpmat.c: |- C = ( N Mat P )


  assert |- ( ( N e. Fin /\ R e. Ring ) -> ( 0g ` C ) e. S )

  proof
    cN
    cfn
    wcel
    cR
    crg
    wcel
    wa
    cS
    cC
    csubg
    cfv
    wcel
    cC
    c0g
    cfv
    #
    cS
    wcel
    cC
    cP
    cR
    cS
    cN
    0elcpmat.s
    0elcpmat.p
    0elcpmat.c
    cpmatsubgpmat
    cS
    cC
    @0
    @0
    eqid
    subg0cl
    syl
end
