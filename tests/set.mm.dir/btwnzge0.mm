include "cr.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "cc0.mm"
include "cfl.mm"
include "cfv.mm"
include "wb.mm"
include "0z.mm"
include "flge.mm"
include "mpan2.mm"
include "ad2antrr.mm"
include "wceq.mm"
include "flbi.mm"
include "biimpar.mm"
include "breq2d.mm"
include "bitrd.mm"

theorem btwnzge0
  let cA: class A
  let cN: class N


  assert |- ( ( ( A e. RR /\ N e. ZZ ) /\ ( N <_ A /\ A < ( N + 1 ) ) ) -> ( 0 <_ A <-> 0 <_ N ) )

  proof
    cA
    cr
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cN
    cA
    cle
    wbr
    cA
    cN
    c1
    caddc
    co
    clt
    wbr
    wa
    #
    wa
    #
    cc0
    cA
    cle
    wbr
    #
    cc0
    cA
    cfl
    cfv
    #
    cle
    wbr
    #
    cc0
    cN
    cle
    wbr
    @0
    @5
    @7
    wb
    #
    @1
    @3
    @0
    cc0
    cz
    wcel
    @8
    0z
    cA
    cc0
    flge
    mpan2
    ad2antrr
    @4
    @6
    cN
    cc0
    cle
    @2
    @6
    cN
    wceq
    @3
    cA
    cN
    flbi
    biimpar
    breq2d
    bitrd
end
