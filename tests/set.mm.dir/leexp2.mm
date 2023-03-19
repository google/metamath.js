include "cr.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wn.mm"
include "cexp.mm"
include "co.mm"
include "cle.mm"
include "wb.mm"
include "3ancomb.mm"
include "ltexp2.mm"
include "sylanb.mm"
include "notbid.mm"
include "simpl2.mm"
include "simpl3.mm"
include "zre.mm"
include "lenlt.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "cc0.mm"
include "wne.mm"
include "simpl1.mm"
include "0red.mm"
include "1red.mm"
include "0lt1.mm"
include "a1i.mm"
include "simpr.mm"
include "lttrd.mm"
include "gt0ne0d.mm"
include "reexpclz.mm"
include "syl3anc.mm"
include "lenltd.mm"
include "3bitr4d.mm"

theorem leexp2
  let cA: class A
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( A e. RR /\ M e. ZZ /\ N e. ZZ ) /\ 1 < A ) -> ( M <_ N <-> ( A ^ M ) <_ ( A ^ N ) ) )

  proof
    cA
    cr
    wcel
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    #
    c1
    cA
    clt
    wbr
    #
    wa
    #
    cN
    cM
    clt
    wbr
    #
    wn
    #
    cA
    cN
    cexp
    co
    #
    cA
    cM
    cexp
    co
    #
    clt
    wbr
    #
    wn
    cM
    cN
    cle
    wbr
    #
    @9
    @8
    cle
    wbr
    @5
    @6
    @10
    @3
    @0
    @2
    @1
    w3a
    @4
    @6
    @10
    wb
    @0
    @1
    @2
    3ancomb
    cA
    cN
    cM
    ltexp2
    sylanb
    notbid
    @5
    @1
    @2
    @11
    @7
    wb
    #
    @0
    @1
    @2
    @4
    simpl2
    #
    @0
    @1
    @2
    @4
    simpl3
    #
    @1
    cM
    cr
    wcel
    cN
    cr
    wcel
    @12
    @2
    cM
    zre
    cN
    zre
    cM
    cN
    lenlt
    syl2an
    syl2anc
    @5
    @9
    @8
    @5
    @0
    cA
    cc0
    wne
    #
    @1
    @9
    cr
    wcel
    @0
    @1
    @2
    @4
    simpl1
    #
    @5
    cA
    @5
    cc0
    c1
    cA
    @5
    0red
    @5
    1red
    @16
    cc0
    c1
    clt
    wbr
    @5
    0lt1
    a1i
    @3
    @4
    simpr
    lttrd
    gt0ne0d
    #
    @13
    cA
    cM
    reexpclz
    syl3anc
    @5
    @0
    @15
    @2
    @8
    cr
    wcel
    @16
    @17
    @14
    cA
    cN
    reexpclz
    syl3anc
    lenltd
    3bitr4d
end
