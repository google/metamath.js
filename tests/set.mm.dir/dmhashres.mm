include "chash.mm"
include "cres.mm"
include "cdm.mm"
include "cin.mm"
include "cvv.mm"
include "dmres.mm"
include "cn0.mm"
include "cpnf.mm"
include "csn.mm"
include "cun.mm"
include "hashf.mm"
include "fdmi.mm"
include "ineq2i.mm"
include "inv1.mm"
include "3eqtri.mm"

theorem dmhashres
  let cA: class A


  assert |- dom ( # |` A ) = A

  proof
    chash
    cA
    cres
    cdm
    cA
    chash
    cdm
    #
    cin
    cA
    cvv
    cin
    cA
    chash
    cA
    dmres
    @0
    cvv
    cA
    cvv
    cn0
    cpnf
    csn
    cun
    chash
    hashf
    fdmi
    ineq2i
    cA
    inv1
    3eqtri
end
