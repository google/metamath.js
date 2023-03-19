include "wbr.mm"
include "wsbc.mm"
include "csb.mm"
include "sbcbr123.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "csbconstg.mm"
include "breq12d.mm"
include "wn.mm"
include "c0.mm"
include "br0.mm"
include "csbprc.mm"
include "breqd.mm"
include "mtbiri.mm"
include "2falsed.mm"
include "pm2.61i.mm"
include "bitri.mm"

theorem sbcbr
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R

  disjoint B x
  disjoint C x
  assert |- ( [. A / x ]. B R C <-> B [_ A / x ]_ R C )

  proof
    cB
    cC
    cR
    wbr
    vx
    cA
    wsbc
    vx
    cA
    cB
    csb
    #
    vx
    cA
    cC
    csb
    #
    vx
    cA
    cR
    csb
    #
    wbr
    #
    cB
    cC
    @2
    wbr
    #
    vx
    cA
    cB
    cC
    cR
    sbcbr123
    cA
    cvv
    wcel
    #
    @3
    @4
    wb
    @5
    @0
    cB
    @1
    cC
    @2
    vx
    cA
    cB
    cvv
    csbconstg
    vx
    cA
    cC
    cvv
    csbconstg
    breq12d
    @5
    wn
    #
    @3
    @4
    @6
    @3
    @0
    @1
    c0
    wbr
    @0
    @1
    br0
    @6
    @2
    c0
    @0
    @1
    vx
    cA
    cR
    csbprc
    #
    breqd
    mtbiri
    @6
    @4
    cB
    cC
    c0
    wbr
    cB
    cC
    br0
    @6
    @2
    c0
    cB
    cC
    @7
    breqd
    mtbiri
    2falsed
    pm2.61i
    bitri
end
