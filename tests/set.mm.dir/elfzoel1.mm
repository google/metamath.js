include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cz.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "ne0i.mm"
include "cxp.mm"
include "cpw.mm"
include "fzof.mm"
include "fdmi.mm"
include "ndmov.mm"
include "necon1ai.mm"
include "syl.mm"
include "simpld.mm"

theorem elfzoel1
  let cA: class A
  let cB: class B
  let cC: class C
  let vm: setvar m
  let vn: setvar n
  let cN: class N
  let cM: class M


  assert |- ( A e. ( B ..^ C ) -> B e. ZZ )

  proof
    cA
    cB
    cC
    cfzo
    co
    #
    wcel
    #
    cB
    cz
    wcel
    #
    cC
    cz
    wcel
    #
    @1
    @0
    c0
    wne
    @2
    @3
    wa
    #
    @0
    cA
    ne0i
    @4
    @0
    c0
    cB
    cC
    cz
    cfzo
    cz
    cz
    cxp
    cz
    cpw
    cfzo
    fzof
    fdmi
    ndmov
    necon1ai
    syl
    simpld
end
