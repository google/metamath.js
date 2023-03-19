include "cprime.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "cn.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "nnoddn2prm.mm"
include "simprd.mm"

theorem oddn2prm
  let cN: class N


  assert |- ( N e. ( Prime \ { 2 } ) -> -. 2 || N )

  proof
    cN
    cprime
    c2
    csn
    cdif
    wcel
    cN
    cn
    wcel
    c2
    cN
    cdvds
    wbr
    wn
    cN
    nnoddn2prm
    simprd
end
