include "cee.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cmin.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "cle.mm"
include "fzfid.mm"
include "cr.mm"
include "fveere.mm"
include "adantlr.mm"
include "adantll.mm"
include "resubcld.mm"
include "resqcld.mm"
include "sqge0d.mm"
include "fsumge0.mm"
include "syl6breqr.mm"

theorem axsegconlem3
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
  assert |- ( ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) -> 0 <_ S )

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
    wa
    #
    cc0
    c1
    cN
    cfz
    co
    #
    vp
    cv
    #
    cA
    cfv
    #
    @5
    cB
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vp
    csu
    cS
    cle
    @3
    @4
    @9
    vp
    @3
    c1
    cN
    fzfid
    @3
    @5
    @4
    wcel
    #
    wa
    #
    @8
    @11
    @6
    @7
    @1
    @10
    @6
    cr
    wcel
    @2
    cA
    @5
    cN
    fveere
    adantlr
    @2
    @10
    @7
    cr
    wcel
    @1
    cB
    @5
    cN
    fveere
    adantll
    resubcld
    #
    resqcld
    @11
    @8
    @12
    sqge0d
    fsumge0
    axsegconlem2.1
    syl6breqr
end
