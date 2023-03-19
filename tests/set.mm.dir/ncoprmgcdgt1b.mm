include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wrex.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wne.mm"
include "clt.mm"
include "ncoprmgcdne1b.mm"
include "wb.mm"
include "gcdnncl.mm"
include "nngt1ne1.mm"
include "syl.mm"
include "bitr4d.mm"

theorem ncoprmgcdgt1b
  let cA: class A
  let cB: class B
  let vi: setvar i

  disjoint A i
  disjoint B i
  assert |- ( ( A e. NN /\ B e. NN ) -> ( E. i e. ( ZZ>= ` 2 ) ( i || A /\ i || B ) <-> 1 < ( A gcd B ) ) )

  proof
    cA
    cn
    wcel
    cB
    cn
    wcel
    wa
    #
    vi
    cv
    #
    cA
    cdvds
    wbr
    @1
    cB
    cdvds
    wbr
    wa
    vi
    c2
    cuz
    cfv
    wrex
    cA
    cB
    cgcd
    co
    #
    c1
    wne
    #
    c1
    @2
    clt
    wbr
    #
    cA
    cB
    vi
    ncoprmgcdne1b
    @0
    @2
    cn
    wcel
    @4
    @3
    wb
    cA
    cB
    gcdnncl
    @2
    nngt1ne1
    syl
    bitr4d
end
