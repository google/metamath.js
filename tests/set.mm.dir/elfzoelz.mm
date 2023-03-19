include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cz.mm"
include "cpw.mm"
include "elfzoel1.mm"
include "elfzoel2.mm"
include "fzof.mm"
include "fovcl.mm"
include "syl2anc.mm"
include "elpwid.mm"
include "id.mm"
include "sseldd.mm"

theorem elfzoelz
  let cA: class A
  let cB: class B
  let cC: class C
  let vm: setvar m
  let vn: setvar n
  let cN: class N
  let cM: class M


  assert |- ( A e. ( B ..^ C ) -> A e. ZZ )

  proof
    cA
    cB
    cC
    cfzo
    co
    #
    wcel
    #
    @0
    cz
    cA
    @1
    @0
    cz
    @1
    cB
    cz
    wcel
    cC
    cz
    wcel
    @0
    cz
    cpw
    #
    wcel
    cA
    cB
    cC
    elfzoel1
    cA
    cB
    cC
    elfzoel2
    cB
    cC
    @2
    cz
    cz
    cfzo
    fzof
    fovcl
    syl2anc
    elpwid
    @1
    id
    sseldd
end
