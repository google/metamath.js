include "cq.mm"
include "wcel.mm"
include "cnumer.mm"
include "cfv.mm"
include "cz.mm"
include "cdenom.mm"
include "cn.mm"
include "qnumdencl.mm"
include "simpld.mm"

theorem qnumcl
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A e. QQ -> ( numer ` A ) e. ZZ )

  proof
    cA
    cq
    wcel
    cA
    cnumer
    cfv
    cz
    wcel
    cA
    cdenom
    cfv
    cn
    wcel
    cA
    qnumdencl
    simpld
end
