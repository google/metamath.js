include "cwsuc.mm"
include "ccnv.mm"
include "cpred.mm"
include "cinf.mm"
include "df-wsuc.mm"
include "nfcnv.mm"
include "nfpred.mm"
include "nfinf.mm"
include "nfcxfr.mm"

theorem nfwsuc
  let vx: setvar x
  let cA: class A
  let cR: class R
  let cX: class X
  assume nfwsuc.1: |- F/_ x R
  assume nfwsuc.2: |- F/_ x A
  assume nfwsuc.3: |- F/_ x X


  assert |- F/_ x wsuc ( R , A , X )

  proof
    vx
    cA
    cR
    cX
    cwsuc
    cA
    cR
    ccnv
    #
    cX
    cpred
    #
    cA
    cR
    cinf
    cA
    cR
    cX
    df-wsuc
    vx
    @1
    cA
    cR
    vx
    cA
    @0
    cX
    vx
    cR
    nfwsuc.1
    nfcnv
    nfwsuc.2
    nfwsuc.3
    nfpred
    nfwsuc.2
    nfwsuc.1
    nfinf
    nfcxfr
end
