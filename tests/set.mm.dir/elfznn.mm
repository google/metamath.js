include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "cn.mm"
include "elfzelz.mm"
include "elfzle1.mm"
include "elnnz1.mm"
include "sylanbrc.mm"

theorem elfznn
  let cK: class K
  let cN: class N


  assert |- ( K e. ( 1 ... N ) -> K e. NN )

  proof
    cK
    c1
    cN
    cfz
    co
    wcel
    cK
    cz
    wcel
    c1
    cK
    cle
    wbr
    cK
    cn
    wcel
    cK
    c1
    cN
    elfzelz
    cK
    c1
    cN
    elfzle1
    cK
    elnnz1
    sylanbrc
end
