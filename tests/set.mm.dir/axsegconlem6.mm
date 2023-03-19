include "cee.mm"
include "cfv.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "csqrt.mm"
include "cr.mm"
include "axsegconlem4.mm"
include "3adant3.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "axsegconlem5.mm"
include "wa.mm"
include "wceq.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cmin.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "eqeelen.mm"
include "eqeq1i.mm"
include "syl6bbr.mm"
include "wb.mm"
include "axsegconlem2.mm"
include "axsegconlem3.mm"
include "sqrt00.mm"
include "syl2anc.mm"
include "bitr4d.mm"
include "necon3bid.mm"
include "biimp3a.mm"
include "ne0gt0d.mm"

theorem axsegconlem6
  let cA: class A
  let cB: class B
  let cS: class S
  let cN: class N
  let vp: setvar p
  let cC: class C
  let cD: class D
  assume axsegconlem2.1: |- S = sum_ p e. ( 1 ... N ) ( ( ( A ` p ) - ( B ` p ) ) ^ 2 )

  disjoint A p
  disjoint B p
  disjoint N p
  disjoint C p
  disjoint D p
  assert |- ( ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ A =/= B ) -> 0 < ( sqrt ` S ) )

  proof
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cA
    cB
    wne
    #
    w3a
    cS
    csqrt
    cfv
    #
    @1
    @2
    @4
    cr
    wcel
    @3
    cA
    cB
    cS
    cN
    vp
    axsegconlem2.1
    axsegconlem4
    3adant3
    @1
    @2
    cc0
    @4
    cle
    wbr
    @3
    cA
    cB
    cS
    cN
    vp
    axsegconlem2.1
    axsegconlem5
    3adant3
    @1
    @2
    @3
    @4
    cc0
    wne
    @1
    @2
    wa
    #
    cA
    cB
    @4
    cc0
    @5
    cA
    cB
    wceq
    #
    cS
    cc0
    wceq
    #
    @4
    cc0
    wceq
    #
    @5
    @6
    c1
    cN
    cfz
    co
    vp
    cv
    #
    cA
    cfv
    @9
    cB
    cfv
    cmin
    co
    c2
    cexp
    co
    vp
    csu
    #
    cc0
    wceq
    @7
    cA
    cB
    vp
    cN
    eqeelen
    cS
    @10
    cc0
    axsegconlem2.1
    eqeq1i
    syl6bbr
    @5
    cS
    cr
    wcel
    cc0
    cS
    cle
    wbr
    @8
    @7
    wb
    cA
    cB
    cS
    cN
    vp
    axsegconlem2.1
    axsegconlem2
    cA
    cB
    cS
    cN
    vp
    axsegconlem2.1
    axsegconlem3
    cS
    sqrt00
    syl2anc
    bitr4d
    necon3bid
    biimp3a
    ne0gt0d
end
