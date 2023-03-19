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
include "simp3bi.mm"
include "syl6.mm"

theorem stle1
  let cA: class A
  let cS: class S
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let cB: class B


  assert |- ( S e. States -> ( A e. CH -> ( S ` A ) <_ 1 ) )

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
    @0
    c1
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
    cc0
    @0
    cle
    wbr
    @2
    cc0
    c1
    @0
    0re
    1re
    elicc2i
    simp3bi
    syl6
end
