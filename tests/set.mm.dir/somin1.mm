include "wor.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cif.mm"
include "cid.mm"
include "cun.mm"
include "wceq.mm"
include "wo.mm"
include "iftrue.mm"
include "olcd.mm"
include "adantl.mm"
include "wn.mm"
include "sotric.mm"
include "orcom.mm"
include "eqcom.mm"
include "orbi2i.mm"
include "bitri.mm"
include "notbii.mm"
include "syl6bb.mm"
include "con2bid.mm"
include "biimpar.mm"
include "wb.mm"
include "iffalse.mm"
include "breq1.mm"
include "eqeq1.mm"
include "orbi12d.mm"
include "syl.mm"
include "mpbird.mm"
include "pm2.61dan.mm"
include "poleloe.mm"
include "ad2antrl.mm"

theorem somin1
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X


  assert |- ( ( R Or X /\ ( A e. X /\ B e. X ) ) -> if ( A R B , A , B ) ( R u. _I ) A )

  proof
    cX
    cR
    wor
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    wa
    wa
    #
    cA
    cB
    cR
    wbr
    #
    cA
    cB
    cif
    #
    cA
    cR
    cid
    cun
    wbr
    #
    @5
    cA
    cR
    wbr
    #
    @5
    cA
    wceq
    #
    wo
    #
    @3
    @4
    @9
    @4
    @9
    @3
    @4
    @8
    @7
    @4
    cA
    cB
    iftrue
    olcd
    adantl
    @3
    @4
    wn
    #
    wa
    @9
    cB
    cA
    cR
    wbr
    #
    cB
    cA
    wceq
    #
    wo
    #
    @3
    @13
    @10
    @3
    @4
    @13
    @3
    @4
    cA
    cB
    wceq
    #
    @11
    wo
    #
    wn
    @13
    wn
    cX
    cA
    cB
    cR
    sotric
    @15
    @13
    @15
    @11
    @14
    wo
    @13
    @14
    @11
    orcom
    @14
    @12
    @11
    cA
    cB
    eqcom
    orbi2i
    bitri
    notbii
    syl6bb
    con2bid
    biimpar
    @10
    @9
    @13
    wb
    #
    @3
    @10
    @5
    cB
    wceq
    #
    @16
    @4
    cA
    cB
    iffalse
    @17
    @7
    @11
    @8
    @12
    @5
    cB
    cA
    cR
    breq1
    @5
    cB
    cA
    eqeq1
    orbi12d
    syl
    adantl
    mpbird
    pm2.61dan
    @1
    @6
    @9
    wb
    @0
    @2
    @5
    cA
    cR
    cX
    poleloe
    ad2antrl
    mpbird
end
