include "cdiv.mm"
include "co.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "wcel.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "clt.mm"
include "w3a.mm"
include "0re.mm"
include "1re.mm"
include "elicc2i.mm"
include "df-3an.mm"
include "bitri.mm"
include "cmul.mm"
include "wb.mm"
include "ledivmul.mm"
include "mp3an2.mm"
include "adantlr.mm"
include "simpll.mm"
include "simprl.mm"
include "wne.mm"
include "gt0ne0.mm"
include "adantl.mm"
include "redivcld.mm"
include "divge0.mm"
include "jca.mm"
include "biantrurd.mm"
include "cc.mm"
include "recn.mm"
include "ad2antrl.mm"
include "mulid1d.mm"
include "breq2d.mm"
include "3bitr3d.mm"
include "syl5bb.mm"

theorem divelunit
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ 0 <_ A ) /\ ( B e. RR /\ 0 < B ) ) -> ( ( A / B ) e. ( 0 [,] 1 ) <-> A <_ B ) )

  proof
    cA
    cB
    cdiv
    co
    #
    cc0
    c1
    cicc
    co
    wcel
    #
    @0
    cr
    wcel
    #
    cc0
    @0
    cle
    wbr
    #
    wa
    #
    @0
    c1
    cle
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
    cle
    wbr
    #
    wa
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
    wa
    #
    cA
    cB
    cle
    wbr
    #
    @1
    @2
    @3
    @5
    w3a
    @6
    cc0
    c1
    @0
    0re
    1re
    elicc2i
    @2
    @3
    @5
    df-3an
    bitri
    @13
    @5
    cA
    cB
    c1
    cmul
    co
    #
    cle
    wbr
    #
    @6
    @14
    @7
    @12
    @5
    @16
    wb
    #
    @8
    @7
    c1
    cr
    wcel
    @12
    @17
    1re
    cA
    c1
    cB
    ledivmul
    mp3an2
    adantlr
    @13
    @4
    @5
    @13
    @2
    @3
    @13
    cA
    cB
    @7
    @8
    @12
    simpll
    @9
    @10
    @11
    simprl
    @12
    cB
    cc0
    wne
    @9
    cB
    gt0ne0
    adantl
    redivcld
    cA
    cB
    divge0
    jca
    biantrurd
    @13
    @15
    cB
    cA
    cle
    @13
    cB
    @10
    cB
    cc
    wcel
    @9
    @11
    cB
    recn
    ad2antrl
    mulid1d
    breq2d
    3bitr3d
    syl5bb
end
