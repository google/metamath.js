include "cn0.mm"
include "wcel.mm"
include "cprmo.mm"
include "cfv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cprime.mm"
include "cif.mm"
include "cprod.mm"
include "cn.mm"
include "prmoval.mm"
include "fzfid.mm"
include "wa.mm"
include "elfznn.mm"
include "adantl.mm"
include "1nn.mm"
include "a1i.mm"
include "ifcld.mm"
include "fprodnncl.mm"
include "eqeltrd.mm"

theorem prmocl
  let cN: class N
  let vk: setvar k
  let vn: setvar n


  assert |- ( N e. NN0 -> ( #p ` N ) e. NN )

  proof
    cN
    cn0
    wcel
    #
    cN
    cprmo
    cfv
    c1
    cN
    cfz
    co
    #
    vk
    cv
    #
    cprime
    wcel
    #
    @2
    c1
    cif
    #
    vk
    cprod
    cn
    vk
    cN
    prmoval
    @0
    @1
    @4
    vk
    @0
    c1
    cN
    fzfid
    @0
    @2
    @1
    wcel
    #
    wa
    #
    @3
    @2
    c1
    cn
    @5
    @2
    cn
    wcel
    @0
    @2
    cN
    elfznn
    adantl
    c1
    cn
    wcel
    @6
    1nn
    a1i
    ifcld
    fprodnncl
    eqeltrd
end
