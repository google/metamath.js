include "cn0.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cbits.mm"
include "cres.mm"
include "wf1o.mm"
include "ccnv.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "csu.mm"
include "cmpt.mm"
include "wceq.mm"
include "bitsf1ocnv.mm"
include "simpli.mm"

theorem bitsf1o
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let cN: class N


  assert |- ( bits |` NN0 ) : NN0 -1-1-onto-> ( ~P NN0 i^i Fin )

  proof
    cn0
    cn0
    cpw
    cfn
    cin
    #
    cbits
    cn0
    cres
    #
    wf1o
    @1
    ccnv
    vx
    @0
    vx
    cv
    c2
    vn
    cv
    cexp
    co
    vn
    csu
    cmpt
    wceq
    vx
    vn
    bitsf1ocnv
    simpli
end
