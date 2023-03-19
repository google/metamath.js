include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cdp.mm"
include "clt.mm"
include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "wbr.mm"
include "nn0rei.mm"
include "wa.mm"
include "10re.mm"
include "10pos.mm"
include "pm3.2i.mm"
include "elrp.mm"
include "mpbir.mm"
include "rpdivcl.mm"
include "mp2an.mm"
include "ltaddrp.mm"
include "rpre.mm"
include "ax-mp.mm"
include "dpval2.mm"
include "breqtrri.mm"

theorem dpgti
  let cA: class A
  let cB: class B
  assume dpgti.a: |- A e. NN0
  assume dpgti.b: |- B e. RR+


  assert |- A < ( A . B )

  proof
    cA
    cA
    cB
    c1
    cc0
    cdc
    #
    cdiv
    co
    #
    caddc
    co
    #
    cA
    cB
    cdp
    co
    clt
    cA
    cr
    wcel
    @1
    crp
    wcel
    #
    cA
    @2
    clt
    wbr
    cA
    dpgti.a
    nn0rei
    cB
    crp
    wcel
    #
    @0
    crp
    wcel
    #
    @3
    dpgti.b
    @5
    @0
    cr
    wcel
    #
    cc0
    @0
    clt
    wbr
    #
    wa
    @6
    @7
    10re
    10pos
    pm3.2i
    @0
    elrp
    mpbir
    cB
    @0
    rpdivcl
    mp2an
    cA
    @1
    ltaddrp
    mp2an
    cA
    cB
    dpgti.a
    @4
    cB
    cr
    wcel
    dpgti.b
    cB
    rpre
    ax-mp
    dpval2
    breqtrri
end
