include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "exmidd.mm"

theorem zeo3
  let cN: class N


  assert |- ( N e. ZZ -> ( 2 || N \/ -. 2 || N ) )

  proof
    cN
    cz
    wcel
    c2
    cN
    cdvds
    wbr
    exmidd
end
