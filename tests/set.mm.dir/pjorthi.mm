include "cch.mm"
include "wcel.mm"
include "csh.mm"
include "cpjh.mm"
include "cfv.mm"
include "cort.mm"
include "wa.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "chsh.mm"
include "chil.mm"
include "axpjcl.mm"
include "mpan2.mm"
include "choccl.mm"
include "sylancl.mm"
include "jca.mm"
include "shocorth.mm"
include "sylc.mm"

theorem pjorthi
  let cA: class A
  let cB: class B
  let cH: class H
  assume pjorth.1: |- A e. ~H
  assume pjorth.2: |- B e. ~H


  assert |- ( H e. CH -> ( ( ( projh ` H ) ` A ) .ih ( ( projh ` ( _|_ ` H ) ) ` B ) ) = 0 )

  proof
    cH
    cch
    wcel
    #
    cH
    csh
    wcel
    cA
    cH
    cpjh
    cfv
    cfv
    #
    cH
    wcel
    #
    cB
    cH
    cort
    cfv
    #
    cpjh
    cfv
    cfv
    #
    @3
    wcel
    #
    wa
    @1
    @4
    csp
    co
    cc0
    wceq
    cH
    chsh
    @0
    @2
    @5
    @0
    cA
    chil
    wcel
    @2
    pjorth.1
    cA
    cH
    axpjcl
    mpan2
    @0
    @3
    cch
    wcel
    cB
    chil
    wcel
    @5
    cH
    choccl
    pjorth.2
    cB
    @3
    axpjcl
    sylancl
    jca
    @1
    @4
    cH
    shocorth
    sylc
end
