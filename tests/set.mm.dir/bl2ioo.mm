include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cbl.mm"
include "cfv.mm"
include "co.mm"
include "cmin.mm"
include "caddc.mm"
include "cioo.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cabs.mm"
include "wb.mm"
include "remetdval.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "abssub.mm"
include "syl2an.mm"
include "eqtrd.mm"
include "breq1d.mm"
include "adantlr.mm"
include "absdiflt.mm"
include "3expb.mm"
include "ancoms.mm"
include "bitrd.mm"
include "pm5.32da.mm"
include "3anass.mm"
include "syl6bbr.mm"
include "cxr.mm"
include "rexr.mm"
include "cxmt.mm"
include "rexmet.mm"
include "elbl.mm"
include "mp3an1.mm"
include "sylan2.mm"
include "resubcl.mm"
include "readdcl.mm"
include "elioo2.mm"
include "syl2anc.mm"
include "3bitr4d.mm"
include "eqrdv.mm"

theorem bl2ioo
  let cA: class A
  let cB: class B
  let cD: class D
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume remet.1: |- D = ( ( abs o. - ) |` ( RR X. RR ) )


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A ( ball ` D ) B ) = ( ( A - B ) (,) ( A + B ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    vx
    cA
    cB
    cD
    cbl
    cfv
    co
    #
    cA
    cB
    cmin
    co
    #
    cA
    cB
    caddc
    co
    #
    cioo
    co
    #
    @2
    vx
    cv
    #
    cr
    wcel
    #
    cA
    @7
    cD
    co
    #
    cB
    clt
    wbr
    #
    wa
    #
    @8
    @4
    @7
    clt
    wbr
    #
    @7
    @5
    clt
    wbr
    #
    w3a
    #
    @7
    @3
    wcel
    #
    @7
    @6
    wcel
    #
    @2
    @11
    @8
    @12
    @13
    wa
    #
    wa
    @14
    @2
    @8
    @10
    @17
    @2
    @8
    wa
    @10
    @7
    cA
    cmin
    co
    cabs
    cfv
    #
    cB
    clt
    wbr
    #
    @17
    @0
    @8
    @10
    @19
    wb
    @1
    @0
    @8
    wa
    #
    @9
    @18
    cB
    clt
    @20
    @9
    cA
    @7
    cmin
    co
    cabs
    cfv
    #
    @18
    cA
    @7
    cD
    remet.1
    remetdval
    @0
    cA
    cc
    wcel
    @7
    cc
    wcel
    @21
    @18
    wceq
    @8
    cA
    recn
    @7
    recn
    cA
    @7
    abssub
    syl2an
    eqtrd
    breq1d
    adantlr
    @8
    @2
    @19
    @17
    wb
    #
    @8
    @0
    @1
    @22
    @7
    cA
    cB
    absdiflt
    3expb
    ancoms
    bitrd
    pm5.32da
    @8
    @12
    @13
    3anass
    syl6bbr
    @1
    @0
    cB
    cxr
    wcel
    #
    @15
    @11
    wb
    #
    cB
    rexr
    cD
    cr
    cxmt
    cfv
    wcel
    @0
    @23
    @24
    cD
    remet.1
    rexmet
    @7
    cD
    cA
    cB
    cr
    elbl
    mp3an1
    sylan2
    @2
    @4
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    @16
    @14
    wb
    #
    cA
    cB
    resubcl
    cA
    cB
    readdcl
    @25
    @4
    cxr
    wcel
    @5
    cxr
    wcel
    @27
    @26
    @4
    rexr
    @5
    rexr
    @4
    @5
    @7
    elioo2
    syl2an
    syl2anc
    3bitr4d
    eqrdv
end
