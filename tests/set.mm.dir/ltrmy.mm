include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "crmy.mm"
include "co.mm"
include "cv.mm"
include "cneg.mm"
include "cn0.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "ltrmynn0.mm"
include "biimpd.mm"
include "cz.mm"
include "wa.mm"
include "frmy.mm"
include "fovcl.mm"
include "zred.mm"
include "rmyneg.mm"
include "oveq2.mm"
include "monotoddzz.mm"

theorem ltrmy
  let cA: class A
  let cM: class M
  let cN: class N
  let va: setvar a
  let vb: setvar b


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. ZZ /\ N e. ZZ ) -> ( M < N <-> ( A rmY M ) < ( A rmY N ) ) )

  proof
    cA
    c2
    cuz
    cfv
    #
    wcel
    #
    va
    vb
    cM
    cN
    cA
    cM
    crmy
    co
    cA
    cN
    crmy
    co
    cA
    va
    cv
    #
    crmy
    co
    #
    cA
    vb
    cv
    #
    crmy
    co
    #
    cA
    @4
    cneg
    #
    crmy
    co
    @1
    @2
    cn0
    wcel
    @4
    cn0
    wcel
    w3a
    @2
    @4
    clt
    wbr
    @3
    @5
    clt
    wbr
    cA
    @2
    @4
    ltrmynn0
    biimpd
    @1
    @2
    cz
    wcel
    wa
    @3
    cA
    @2
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    zred
    cA
    @4
    rmyneg
    @2
    cM
    cA
    crmy
    oveq2
    @2
    cN
    cA
    crmy
    oveq2
    @2
    @4
    cA
    crmy
    oveq2
    @2
    @6
    cA
    crmy
    oveq2
    monotoddzz
end
