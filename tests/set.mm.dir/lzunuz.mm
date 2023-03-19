include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cuz.mm"
include "cfv.mm"
include "cdif.mm"
include "cun.mm"
include "cv.mm"
include "wo.mm"
include "elun.mm"
include "wa.mm"
include "wb.mm"
include "ellz1.mm"
include "3ad2ant1.mm"
include "eluz1.mm"
include "3ad2ant2.mm"
include "orbi12d.mm"
include "clt.mm"
include "cr.mm"
include "zre.mm"
include "adantl.mm"
include "simpl1.mm"
include "zred.mm"
include "lelttric.mm"
include "syl2anc.mm"
include "simpll2.mm"
include "simpll1.mm"
include "peano2zd.mm"
include "ad2antlr.mm"
include "simpll3.mm"
include "zltp1le.mm"
include "3ad2antl1.mm"
include "biimpa.mm"
include "letrd.mm"
include "ex.mm"
include "orim2d.mm"
include "mpd.mm"
include "pm4.71d.mm"
include "andi.mm"
include "syl6rbb.mm"
include "bitrd.mm"
include "syl5bb.mm"
include "eqrdv.mm"

theorem lzunuz
  let cA: class A
  let cB: class B
  let cN: class N
  let va: setvar a


  assert |- ( ( A e. ZZ /\ B e. ZZ /\ B <_ ( A + 1 ) ) -> ( ( ZZ \ ( ZZ>= ` ( A + 1 ) ) ) u. ( ZZ>= ` B ) ) = ZZ )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    cB
    cA
    c1
    caddc
    co
    #
    cle
    wbr
    #
    w3a
    #
    va
    cz
    @2
    cuz
    cfv
    cdif
    #
    cB
    cuz
    cfv
    #
    cun
    #
    cz
    va
    cv
    #
    @7
    wcel
    @8
    @5
    wcel
    #
    @8
    @6
    wcel
    #
    wo
    #
    @4
    @8
    cz
    wcel
    #
    @8
    @5
    @6
    elun
    @4
    @11
    @12
    @8
    cA
    cle
    wbr
    #
    wa
    #
    @12
    cB
    @8
    cle
    wbr
    #
    wa
    #
    wo
    #
    @12
    @4
    @9
    @14
    @10
    @16
    @0
    @1
    @9
    @14
    wb
    @3
    @8
    cA
    ellz1
    3ad2ant1
    @1
    @0
    @10
    @16
    wb
    @3
    cB
    @8
    eluz1
    3ad2ant2
    orbi12d
    @4
    @12
    @12
    @13
    @15
    wo
    #
    wa
    @17
    @4
    @12
    @18
    @4
    @12
    @18
    @4
    @12
    wa
    #
    @13
    cA
    @8
    clt
    wbr
    #
    wo
    #
    @18
    @19
    @8
    cr
    wcel
    #
    cA
    cr
    wcel
    @21
    @12
    @22
    @4
    @8
    zre
    #
    adantl
    @19
    cA
    @0
    @1
    @3
    @12
    simpl1
    zred
    @8
    cA
    lelttric
    syl2anc
    @19
    @20
    @15
    @13
    @19
    @20
    @15
    @19
    @20
    wa
    #
    cB
    @2
    @8
    @24
    cB
    @0
    @1
    @3
    @12
    @20
    simpll2
    zred
    @24
    @2
    @24
    cA
    @0
    @1
    @3
    @12
    @20
    simpll1
    peano2zd
    zred
    @12
    @22
    @4
    @20
    @23
    ad2antlr
    @0
    @1
    @3
    @12
    @20
    simpll3
    @19
    @20
    @2
    @8
    cle
    wbr
    #
    @0
    @1
    @12
    @20
    @25
    wb
    @3
    cA
    @8
    zltp1le
    3ad2antl1
    biimpa
    letrd
    ex
    orim2d
    mpd
    ex
    pm4.71d
    @12
    @13
    @15
    andi
    syl6rbb
    bitrd
    syl5bb
    eqrdv
end
