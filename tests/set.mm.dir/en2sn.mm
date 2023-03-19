include "wcel.mm"
include "csn.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "ensn1g.mm"
include "ensymd.mm"
include "entr.mm"
include "syl2an.mm"

theorem en2sn
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x
  let vy: setvar y
  let cV: class V


  assert |- ( ( A e. C /\ B e. D ) -> { A } ~~ { B } )

  proof
    cA
    cC
    wcel
    cA
    csn
    #
    c1o
    cen
    wbr
    c1o
    cB
    csn
    #
    cen
    wbr
    @0
    @1
    cen
    wbr
    cB
    cD
    wcel
    #
    cA
    cC
    ensn1g
    @2
    @1
    c1o
    cB
    cD
    ensn1g
    ensymd
    @0
    c1o
    @1
    entr
    syl2an
end
