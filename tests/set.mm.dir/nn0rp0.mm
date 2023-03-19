include "cn0.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "nn0re.mm"
include "nn0ge0.mm"
include "elrege0.mm"
include "sylanbrc.mm"

theorem nn0rp0
  let cN: class N


  assert |- ( N e. NN0 -> N e. ( 0 [,) +oo ) )

  proof
    cN
    cn0
    wcel
    cN
    cr
    wcel
    cc0
    cN
    cle
    wbr
    cN
    cc0
    cpnf
    cico
    co
    wcel
    cN
    nn0re
    cN
    nn0ge0
    cN
    elrege0
    sylanbrc
end
