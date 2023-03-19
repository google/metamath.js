include "csup.mm"
include "ccnv.mm"
include "cima.mm"
include "cdif.mm"
include "cun.mm"
include "cuni.mm"
include "dfsup2.mm"
include "nfcnv.mm"
include "nfima.mm"
include "nfdif.mm"
include "nfun.mm"
include "nfuni.mm"
include "nfcxfr.mm"

theorem nfsup
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  assume nfsup.1: |- F/_ x A
  assume nfsup.2: |- F/_ x B
  assume nfsup.3: |- F/_ x R


  assert |- F/_ x sup ( A , B , R )

  proof
    vx
    cA
    cB
    cR
    csup
    cB
    cR
    ccnv
    #
    cA
    cima
    #
    cR
    cB
    @1
    cdif
    #
    cima
    #
    cun
    #
    cdif
    #
    cuni
    cB
    cA
    cR
    dfsup2
    vx
    @5
    vx
    cB
    @4
    nfsup.2
    vx
    @1
    @3
    vx
    @0
    cA
    vx
    cR
    nfsup.3
    nfcnv
    nfsup.1
    nfima
    #
    vx
    cR
    @2
    nfsup.3
    vx
    cB
    @1
    nfsup.2
    @6
    nfdif
    nfima
    nfun
    nfdif
    nfuni
    nfcxfr
end
