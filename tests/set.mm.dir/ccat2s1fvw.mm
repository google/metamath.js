include "cword.mm"
include "wcel.mm"
include "cn0.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "wa.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "wceq.mm"
include "simpl1.mm"
include "simprl.mm"
include "simpr.mm"
include "adantl.mm"
include "ccatw2s1ass.mm"
include "syl3anc.mm"
include "fveq1d.mm"
include "cc0.mm"
include "cfzo.mm"
include "ccat2s1cl.mm"
include "cn.mm"
include "simp2.mm"
include "lencl.mm"
include "3ad2ant1.mm"
include "cle.mm"
include "nn0ge0.mm"
include "cr.mm"
include "wi.mm"
include "0red.mm"
include "nn0red.mm"
include "adantr.mm"
include "lelttr.mm"
include "mpand.mm"
include "3impia.mm"
include "elnnnn0b.mm"
include "sylanbrc.mm"
include "simp3.mm"
include "3jca.mm"
include "elfzo0.mm"
include "sylibr.mm"
include "ccatval1.mm"
include "eqtrd.mm"

theorem ccat2s1fvw
  let cI: class I
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y


  assert |- ( ( ( W e. Word V /\ I e. NN0 /\ I < ( # ` W ) ) /\ ( X e. V /\ Y e. V ) ) -> ( ( ( W ++ <" X "> ) ++ <" Y "> ) ` I ) = ( W ` I ) )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cI
    cn0
    wcel
    #
    cI
    cW
    chash
    cfv
    #
    clt
    wbr
    #
    w3a
    #
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    wa
    #
    wa
    #
    cI
    cW
    cX
    cs1
    #
    cconcat
    co
    cY
    cs1
    #
    cconcat
    co
    #
    cfv
    cI
    cW
    @10
    @11
    cconcat
    co
    #
    cconcat
    co
    #
    cfv
    #
    cI
    cW
    cfv
    #
    @9
    cI
    @12
    @14
    @9
    @1
    @6
    @7
    @12
    @14
    wceq
    @1
    @2
    @4
    @8
    simpl1
    #
    @5
    @6
    @7
    simprl
    @8
    @7
    @5
    @6
    @7
    simpr
    adantl
    cV
    cW
    cX
    cY
    ccatw2s1ass
    syl3anc
    fveq1d
    @9
    @1
    @13
    @0
    wcel
    #
    cI
    cc0
    @3
    cfzo
    co
    wcel
    #
    @15
    @16
    wceq
    @17
    @8
    @18
    @5
    cV
    cX
    cY
    ccat2s1cl
    adantl
    @9
    @2
    @3
    cn
    wcel
    #
    @4
    w3a
    #
    @19
    @5
    @21
    @8
    @5
    @2
    @20
    @4
    @1
    @2
    @4
    simp2
    @5
    @3
    cn0
    wcel
    #
    cc0
    @3
    clt
    wbr
    #
    @20
    @1
    @2
    @22
    @4
    cV
    cW
    lencl
    #
    3ad2ant1
    @1
    @2
    @4
    @23
    @1
    @2
    wa
    #
    cc0
    cI
    cle
    wbr
    #
    @4
    @23
    @2
    @26
    @1
    cI
    nn0ge0
    adantl
    @25
    cc0
    cr
    wcel
    cI
    cr
    wcel
    @3
    cr
    wcel
    #
    @26
    @4
    wa
    @23
    wi
    @25
    0red
    @25
    cI
    @1
    @2
    simpr
    nn0red
    @1
    @27
    @2
    @1
    @3
    @24
    nn0red
    adantr
    cc0
    cI
    @3
    lelttr
    syl3anc
    mpand
    3impia
    @3
    elnnnn0b
    sylanbrc
    @1
    @2
    @4
    simp3
    3jca
    adantr
    cI
    @3
    elfzo0
    sylibr
    cV
    cW
    @13
    cI
    ccatval1
    syl3anc
    eqtrd
end
