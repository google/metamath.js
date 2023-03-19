include "cn.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "cle.mm"
include "wi.mm"
include "nnre.mm"
include "nngt0.mm"
include "jca.mm"
include "c1.mm"
include "nnge1.mm"
include "wb.mm"
include "lediv2.mm"
include "3anidm23.mm"
include "cc.mm"
include "wne.mm"
include "recn.mm"
include "adantr.mm"
include "gt0ne0.mm"
include "divid.mm"
include "breq1d.mm"
include "syl2anc.mm"
include "adantl.mm"
include "bitrd.mm"
include "syl5ibr.mm"
include "syl2anr.mm"

theorem nndivlub
  let cA: class A
  let cB: class B


  assert |- ( ( A e. NN /\ B e. NN ) -> ( ( A / B ) e. NN -> B <_ A ) )

  proof
    cB
    cn
    wcel
    #
    cB
    cr
    wcel
    #
    cc0
    cB
    clt
    wbr
    #
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
    cA
    cB
    cdiv
    co
    #
    cn
    wcel
    #
    cB
    cA
    cle
    wbr
    #
    wi
    cA
    cn
    wcel
    #
    @0
    @1
    @2
    cB
    nnre
    cB
    nngt0
    jca
    @10
    @4
    @5
    cA
    nnre
    cA
    nngt0
    jca
    @8
    @9
    @3
    @6
    wa
    #
    c1
    @7
    cle
    wbr
    #
    @7
    nnge1
    @11
    @9
    cA
    cA
    cdiv
    co
    #
    @7
    cle
    wbr
    #
    @12
    @3
    @6
    @9
    @14
    wb
    cB
    cA
    cA
    lediv2
    3anidm23
    @6
    @14
    @12
    wb
    #
    @3
    @6
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    @15
    @4
    @16
    @5
    cA
    recn
    adantr
    cA
    gt0ne0
    @16
    @17
    wa
    @13
    c1
    @7
    cle
    cA
    divid
    breq1d
    syl2anc
    adantl
    bitrd
    syl5ibr
    syl2anr
end
