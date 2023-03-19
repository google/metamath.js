include "cmzp.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "cof.mm"
include "co.mm"
include "cmul.mm"
include "cmzpcl.mm"
include "cvv.mm"
include "elfvex.mm"
include "adantr.mm"
include "mzpincl.mm"
include "syl.mm"
include "mzpcl34.mm"
include "3expib.mm"
include "mpcom.mm"
include "simpld.mm"

theorem mzpadd
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( ( A e. ( mzPoly ` V ) /\ B e. ( mzPoly ` V ) ) -> ( A oF + B ) e. ( mzPoly ` V ) )

  proof
    cA
    cV
    cmzp
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
    cA
    cB
    caddc
    cof
    co
    @0
    wcel
    #
    cA
    cB
    cmul
    cof
    co
    @0
    wcel
    #
    @0
    cV
    cmzpcl
    cfv
    wcel
    #
    @3
    @4
    @5
    wa
    #
    @3
    cV
    cvv
    wcel
    #
    @6
    @1
    @8
    @2
    cA
    cV
    cmzp
    elfvex
    adantr
    cV
    mzpincl
    syl
    @6
    @1
    @2
    @7
    @0
    cA
    cB
    cV
    mzpcl34
    3expib
    mpcom
    simpld
end
