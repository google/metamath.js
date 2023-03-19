include "cn.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "cdiv.mm"
include "co.mm"
include "cr.mm"
include "cc0.mm"
include "clt.mm"
include "wb.mm"
include "1re.mm"
include "0lt1.mm"
include "pm3.2i.mm"
include "rpregt0.mm"
include "adantl.mm"
include "nnre.mm"
include "nngt0.mm"
include "jca.mm"
include "adantr.mm"
include "lediv2.mm"
include "mp3an2i.mm"
include "wceq.mm"
include "nncn.mm"
include "div1d.mm"
include "breq2d.mm"
include "bitrd.mm"

theorem nnledivrp
  let cA: class A
  let cB: class B


  assert |- ( ( A e. NN /\ B e. RR+ ) -> ( 1 <_ B <-> ( A / B ) <_ A ) )

  proof
    cA
    cn
    wcel
    #
    cB
    crp
    wcel
    #
    wa
    #
    c1
    cB
    cle
    wbr
    #
    cA
    cB
    cdiv
    co
    #
    cA
    c1
    cdiv
    co
    #
    cle
    wbr
    #
    @4
    cA
    cle
    wbr
    c1
    cr
    wcel
    #
    cc0
    c1
    clt
    wbr
    #
    wa
    @2
    cB
    cr
    wcel
    cc0
    cB
    clt
    wbr
    wa
    #
    cA
    cr
    wcel
    #
    cc0
    cA
    clt
    wbr
    #
    wa
    #
    @3
    @6
    wb
    @7
    @8
    1re
    0lt1
    pm3.2i
    @1
    @9
    @0
    cB
    rpregt0
    adantl
    @0
    @12
    @1
    @0
    @10
    @11
    cA
    nnre
    cA
    nngt0
    jca
    adantr
    c1
    cB
    cA
    lediv2
    mp3an2i
    @2
    @5
    cA
    @4
    cle
    @0
    @5
    cA
    wceq
    @1
    @0
    cA
    cA
    nncn
    div1d
    adantr
    breq2d
    bitrd
end
