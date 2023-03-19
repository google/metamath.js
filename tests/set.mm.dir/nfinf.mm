include "cinf.mm"
include "ccnv.mm"
include "csup.mm"
include "df-inf.mm"
include "nfcnv.mm"
include "nfsup.mm"
include "nfcxfr.mm"

theorem nfinf
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  assume nfinf.1: |- F/_ x A
  assume nfinf.2: |- F/_ x B
  assume nfinf.3: |- F/_ x R


  assert |- F/_ x inf ( A , B , R )

  proof
    vx
    cA
    cB
    cR
    cinf
    cA
    cB
    cR
    ccnv
    #
    csup
    cA
    cB
    cR
    df-inf
    vx
    cA
    cB
    @0
    nfinf.1
    nfinf.2
    vx
    cR
    nfinf.3
    nfcnv
    nfsup
    nfcxfr
end
