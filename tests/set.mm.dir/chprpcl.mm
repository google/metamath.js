include "cr.mm"
include "wcel.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cchp.mm"
include "cfv.mm"
include "ccht.mm"
include "chpcl.mm"
include "adantr.mm"
include "chtrpcl.mm"
include "chtlepsi.mm"
include "rpgecld.mm"

theorem chprpcl
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vx: setvar x
  let cN: class N


  assert |- ( ( A e. RR /\ 2 <_ A ) -> ( psi ` A ) e. RR+ )

  proof
    cA
    cr
    wcel
    #
    c2
    cA
    cle
    wbr
    #
    wa
    cA
    cchp
    cfv
    #
    cA
    ccht
    cfv
    #
    @0
    @2
    cr
    wcel
    @1
    cA
    chpcl
    adantr
    cA
    chtrpcl
    @0
    @3
    @2
    cle
    wbr
    @1
    cA
    chtlepsi
    adantr
    rpgecld
end
