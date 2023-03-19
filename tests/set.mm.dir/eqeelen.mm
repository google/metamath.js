include "cee.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "cfz.mm"
include "wral.mm"
include "csu.mm"
include "cc.mm"
include "wb.mm"
include "cr.mm"
include "fveere.mm"
include "adantlr.mm"
include "adantll.mm"
include "resubcld.mm"
include "recnd.mm"
include "sqeq0.mm"
include "syl.mm"
include "subeq0ad.mm"
include "bitrd.mm"
include "ralbidva.mm"
include "fzfid.mm"
include "resqcld.mm"
include "sqge0d.mm"
include "fsum00.mm"
include "eqeefv.mm"
include "3bitr4rd.mm"

theorem eqeelen
  let cA: class A
  let cB: class B
  let vi: setvar i
  let cN: class N

  disjoint N i
  disjoint A i
  disjoint B i
  assert |- ( ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) -> ( A = B <-> sum_ i e. ( 1 ... N ) ( ( ( A ` i ) - ( B ` i ) ) ^ 2 ) = 0 ) )

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
    vi
    cv
    #
    cA
    cfv
    #
    @4
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
    cc0
    wceq
    #
    vi
    c1
    cN
    cfz
    co
    #
    wral
    @5
    @6
    wceq
    #
    vi
    @10
    wral
    @10
    @8
    vi
    csu
    cc0
    wceq
    cA
    cB
    wceq
    @3
    @9
    @11
    vi
    @10
    @3
    @4
    @10
    wcel
    #
    wa
    #
    @9
    @7
    cc0
    wceq
    #
    @11
    @13
    @7
    cc
    wcel
    @9
    @14
    wb
    @13
    @7
    @13
    @5
    @6
    @1
    @12
    @5
    cr
    wcel
    @2
    cA
    @4
    cN
    fveere
    adantlr
    #
    @2
    @12
    @6
    cr
    wcel
    @1
    cB
    @4
    cN
    fveere
    adantll
    #
    resubcld
    #
    recnd
    @7
    sqeq0
    syl
    @13
    @5
    @6
    @13
    @5
    @15
    recnd
    @13
    @6
    @16
    recnd
    subeq0ad
    bitrd
    ralbidva
    @3
    @10
    @8
    vi
    @3
    c1
    cN
    fzfid
    @13
    @7
    @17
    resqcld
    @13
    @7
    @17
    sqge0d
    fsum00
    cA
    cB
    vi
    cN
    eqeefv
    3bitr4rd
end
