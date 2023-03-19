include "cfn.mm"
include "wcel.mm"
include "ccrd.mm"
include "cfv.mm"
include "com.mm"
include "chash.mm"
include "wceq.mm"
include "ccnv.mm"
include "ficardom.mm"
include "hashgval.mm"
include "cn0.mm"
include "wf1o.mm"
include "wi.mm"
include "hashgf1o.mm"
include "f1ocnvfv.mm"
include "mpan.mm"
include "sylc.mm"

theorem hashginv
  let vx: setvar x
  let cA: class A
  let cG: class G
  let vy: setvar y
  let cK: class K
  assume hashgval.1: |- G = ( rec ( ( x e. _V |-> ( x + 1 ) ) , 0 ) |` _om )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint K y
  assert |- ( A e. Fin -> ( `' G ` ( # ` A ) ) = ( card ` A ) )

  proof
    cA
    cfn
    wcel
    cA
    ccrd
    cfv
    #
    com
    wcel
    #
    @0
    cG
    cfv
    cA
    chash
    cfv
    #
    wceq
    #
    @2
    cG
    ccnv
    cfv
    @0
    wceq
    #
    cA
    ficardom
    vx
    cA
    cG
    hashgval.1
    hashgval
    com
    cn0
    cG
    wf1o
    @1
    @3
    @4
    wi
    vx
    cG
    hashgval.1
    hashgf1o
    com
    cn0
    @0
    @2
    cG
    f1ocnvfv
    mpan
    sylc
end
