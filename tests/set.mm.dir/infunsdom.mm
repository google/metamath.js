include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "csdm.mm"
include "cun.mm"
include "sdomdom.mm"
include "infunsdom1.mm"
include "anass1rs.mm"
include "adantlrl.mm"
include "sylan2.mm"
include "wn.mm"
include "wb.mm"
include "simpll.mm"
include "ad2antll.mm"
include "numdom.mm"
include "syl2anc.mm"
include "ad2antrl.mm"
include "domtri2.mm"
include "biimpar.mm"
include "uncom.mm"
include "syl5eqbr.mm"
include "adantlrr.mm"
include "syldan.mm"
include "pm2.61dan.mm"

theorem infunsdom
  let cA: class A
  let cB: class B
  let cX: class X


  assert |- ( ( ( X e. dom card /\ _om ~<_ X ) /\ ( A ~< X /\ B ~< X ) ) -> ( A u. B ) ~< X )

  proof
    cX
    ccrd
    cdm
    #
    wcel
    #
    com
    cX
    cdom
    wbr
    #
    wa
    #
    cA
    cX
    csdm
    wbr
    #
    cB
    cX
    csdm
    wbr
    #
    wa
    #
    wa
    #
    cA
    cB
    csdm
    wbr
    #
    cA
    cB
    cun
    #
    cX
    csdm
    wbr
    #
    @8
    @7
    cA
    cB
    cdom
    wbr
    #
    @10
    cA
    cB
    sdomdom
    @3
    @5
    @11
    @10
    @4
    @3
    @11
    @5
    @10
    cA
    cB
    cX
    infunsdom1
    anass1rs
    adantlrl
    sylan2
    @7
    @8
    wn
    #
    cB
    cA
    cdom
    wbr
    #
    @10
    @7
    @13
    @12
    @7
    cB
    @0
    wcel
    #
    cA
    @0
    wcel
    #
    @13
    @12
    wb
    @7
    @1
    cB
    cX
    cdom
    wbr
    #
    @14
    @1
    @2
    @6
    simpll
    #
    @5
    @16
    @3
    @4
    cB
    cX
    sdomdom
    ad2antll
    cX
    cB
    numdom
    syl2anc
    @7
    @1
    cA
    cX
    cdom
    wbr
    #
    @15
    @17
    @4
    @18
    @3
    @5
    cA
    cX
    sdomdom
    ad2antrl
    cX
    cA
    numdom
    syl2anc
    cB
    cA
    domtri2
    syl2anc
    biimpar
    @3
    @4
    @13
    @10
    @5
    @3
    @13
    @4
    @10
    @3
    @13
    @4
    wa
    wa
    @9
    cB
    cA
    cun
    cX
    csdm
    cA
    cB
    uncom
    cB
    cA
    cX
    infunsdom1
    syl5eqbr
    anass1rs
    adantlrr
    syldan
    pm2.61dan
end
