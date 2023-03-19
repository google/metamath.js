include "cpred.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "df-pred.mm"
include "nfcnv.mm"
include "nfsn.mm"
include "nfima.mm"
include "nfin.mm"
include "nfcxfr.mm"

theorem nfpred
  let vx: setvar x
  let cA: class A
  let cR: class R
  let cX: class X
  assume nfpred.1: |- F/_ x R
  assume nfpred.2: |- F/_ x A
  assume nfpred.3: |- F/_ x X


  assert |- F/_ x Pred ( R , A , X )

  proof
    vx
    cA
    cR
    cX
    cpred
    cA
    cR
    ccnv
    #
    cX
    csn
    #
    cima
    #
    cin
    cA
    cR
    cX
    df-pred
    vx
    cA
    @2
    nfpred.2
    vx
    @0
    @1
    vx
    cR
    nfpred.1
    nfcnv
    vx
    cX
    nfpred.3
    nfsn
    nfima
    nfin
    nfcxfr
end
