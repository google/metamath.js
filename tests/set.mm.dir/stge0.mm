include "cst.mm"
include "wcel.mm"
include "cch.mm"
include "cfv.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "sticl.mm"
include "cr.mm"
include "0re.mm"
include "1re.mm"
include "elicc2i.mm"
include "simp2bi.mm"
include "syl6.mm"

theorem stge0
  let cA: class A
  let cS: class S
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let cB: class B


  assert |- ( S e. States -> ( A e. CH -> 0 <_ ( S ` A ) ) )

  proof
    cS
    cst
    wcel
    cA
    cch
    wcel
    cA
    cS
    cfv
    #
    cc0
    c1
    cicc
    co
    wcel
    #
    cc0
    @0
    cle
    wbr
    #
    cA
    cS
    sticl
    @1
    @0
    cr
    wcel
    @2
    @0
    c1
    cle
    wbr
    cc0
    c1
    @0
    0re
    1re
    elicc2i
    simp2bi
    syl6
end
