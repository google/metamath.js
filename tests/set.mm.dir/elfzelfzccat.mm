include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "caddc.mm"
include "cconcat.mm"
include "cn0.mm"
include "wi.mm"
include "lencl.mm"
include "elfz0add.mm"
include "syl2an.mm"
include "ccatlen.mm"
include "oveq2d.mm"
include "eleq2d.mm"
include "sylibrd.mm"

theorem elfzelfzccat
  let cA: class A
  let cB: class B
  let cN: class N
  let cV: class V


  assert |- ( ( A e. Word V /\ B e. Word V ) -> ( N e. ( 0 ... ( # ` A ) ) -> N e. ( 0 ... ( # ` ( A ++ B ) ) ) ) )

  proof
    cA
    cV
    cword
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    cN
    cc0
    cA
    chash
    cfv
    #
    cfz
    co
    wcel
    #
    cN
    cc0
    @4
    cB
    chash
    cfv
    #
    caddc
    co
    #
    cfz
    co
    #
    wcel
    #
    cN
    cc0
    cA
    cB
    cconcat
    co
    chash
    cfv
    #
    cfz
    co
    #
    wcel
    @1
    @4
    cn0
    wcel
    @6
    cn0
    wcel
    @5
    @9
    wi
    @2
    cV
    cA
    lencl
    cV
    cB
    lencl
    @4
    @6
    cN
    elfz0add
    syl2an
    @3
    @11
    @8
    cN
    @3
    @10
    @7
    cc0
    cfz
    cV
    cA
    cB
    ccatlen
    oveq2d
    eleq2d
    sylibrd
end
