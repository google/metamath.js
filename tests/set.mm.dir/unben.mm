include "cn.mm"
include "wss.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "com.mm"
include "cen.mm"
include "cvv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmpt.mm"
include "crdg.mm"
include "cres.mm"
include "eqid.mm"
include "unbenlem.mm"
include "nnenom.mm"
include "ensymi.mm"
include "entr.mm"
include "sylancl.mm"

theorem unben
  let cA: class A
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x

  disjoint m n
  disjoint A m
  disjoint A n
  disjoint m x
  disjoint n x
  disjoint A x
  assert |- ( ( A C_ NN /\ A. m e. NN E. n e. A m < n ) -> A ~~ NN )

  proof
    cA
    cn
    wss
    vm
    cv
    vn
    cv
    clt
    wbr
    vn
    cA
    wrex
    vm
    cn
    wral
    wa
    cA
    com
    cen
    wbr
    com
    cn
    cen
    wbr
    cA
    cn
    cen
    wbr
    vx
    cA
    vm
    vn
    vx
    cvv
    vx
    cv
    c1
    caddc
    co
    cmpt
    c1
    crdg
    com
    cres
    #
    @0
    eqid
    unbenlem
    cn
    com
    nnenom
    ensymi
    cA
    com
    cn
    entr
    sylancl
end
