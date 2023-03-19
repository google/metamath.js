include "cee.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cmin.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "cr.mm"
include "fzfid.mm"
include "fveere.mm"
include "resubcl.mm"
include "resqcld.mm"
include "syl2an.mm"
include "anandirs.mm"
include "fsumrecl.mm"
include "syl5eqel.mm"

theorem axsegconlem2
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
  assert |- ( ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) -> S e. RR )

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
    cS
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
    cr
    axsegconlem2.1
    @3
    @4
    @9
    vp
    @3
    c1
    cN
    fzfid
    @1
    @2
    @5
    @4
    wcel
    #
    @9
    cr
    wcel
    #
    @1
    @10
    wa
    @6
    cr
    wcel
    #
    @7
    cr
    wcel
    #
    @11
    @2
    @10
    wa
    cA
    @5
    cN
    fveere
    cB
    @5
    cN
    fveere
    @12
    @13
    wa
    @8
    @6
    @7
    resubcl
    resqcld
    syl2an
    anandirs
    fsumrecl
    syl5eqel
end
