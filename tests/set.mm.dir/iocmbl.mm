include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cioc.mm"
include "co.mm"
include "cvol.mm"
include "cdm.mm"
include "w3a.mm"
include "cioo.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "rexr.mm"
include "ioounsn.mm"
include "syl3an2.mm"
include "ioombl.mm"
include "cicc.mm"
include "iccid.mm"
include "syl.mm"
include "iccmbl.mm"
include "anidms.mm"
include "eqeltrrd.mm"
include "adantl.mm"
include "unmbl.mm"
include "sylancr.mm"
include "3adant3.mm"
include "3expa.mm"
include "wn.mm"
include "cle.mm"
include "wb.mm"
include "id.mm"
include "xrlenlt.mm"
include "syl2anr.mm"
include "biimp3ar.mm"
include "c0.mm"
include "ioc0.mm"
include "0mbl.mm"
include "syl6eqel.mm"
include "syld3an3.mm"
include "pm2.61dan.mm"

theorem iocmbl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR ) -> ( A (,] B ) e. dom vol )

  proof
    cA
    cxr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cA
    cB
    clt
    wbr
    #
    cA
    cB
    cioc
    co
    #
    cvol
    cdm
    #
    wcel
    #
    @0
    @1
    @3
    @6
    @0
    @1
    @3
    w3a
    cA
    cB
    cioo
    co
    #
    cB
    csn
    #
    cun
    #
    @4
    @5
    @1
    @0
    cB
    cxr
    wcel
    #
    @3
    @9
    @4
    wceq
    cB
    rexr
    #
    cA
    cB
    ioounsn
    syl3an2
    @0
    @1
    @9
    @5
    wcel
    #
    @3
    @2
    @7
    @5
    wcel
    @8
    @5
    wcel
    #
    @12
    cA
    cB
    ioombl
    @1
    @13
    @0
    @1
    cB
    cB
    cicc
    co
    #
    @8
    @5
    @1
    @10
    @14
    @8
    wceq
    @11
    cB
    iccid
    syl
    @1
    @14
    @5
    wcel
    cB
    cB
    iccmbl
    anidms
    eqeltrrd
    adantl
    @7
    @8
    unmbl
    sylancr
    3adant3
    eqeltrrd
    3expa
    @0
    @1
    @3
    wn
    #
    @6
    @0
    @1
    @15
    cB
    cA
    cle
    wbr
    #
    @6
    @0
    @1
    @16
    @15
    @1
    @10
    @0
    @16
    @15
    wb
    @0
    @11
    @0
    id
    cB
    cA
    xrlenlt
    syl2anr
    biimp3ar
    @0
    @1
    @16
    w3a
    @4
    c0
    @5
    @1
    @0
    @10
    @16
    @4
    c0
    wceq
    #
    @11
    @0
    @10
    @17
    @16
    cA
    cB
    ioc0
    biimp3ar
    syl3an2
    0mbl
    syl6eqel
    syld3an3
    3expa
    pm2.61dan
end
