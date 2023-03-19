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
include "cs2.mm"
include "wceq.mm"
include "simp1.mm"
include "anim1i.mm"
include "3anass.mm"
include "sylibr.mm"
include "ccatw2s1ccatws2.mm"
include "fveq1d.mm"
include "syl.mm"
include "cc0.mm"
include "cfzo.mm"
include "adantr.mm"
include "s2cl.mm"
include "adantl.mm"
include "cz.mm"
include "simp2.mm"
include "lencl.mm"
include "nn0zd.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "elfzo0z.mm"
include "syl3anbrc.mm"
include "ccatval1.mm"
include "syl3anc.mm"
include "eqtrd.mm"

theorem ccat2s1fvwALT
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
    cconcat
    co
    cY
    cs1
    cconcat
    co
    #
    cfv
    #
    cI
    cW
    cX
    cY
    cs2
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
    @1
    @6
    @7
    w3a
    #
    @11
    @14
    wceq
    @9
    @1
    @8
    wa
    @16
    @5
    @1
    @8
    @1
    @2
    @4
    simp1
    #
    anim1i
    @1
    @6
    @7
    3anass
    sylibr
    @16
    cI
    @10
    @13
    cV
    cW
    cX
    cY
    ccatw2s1ccatws2
    fveq1d
    syl
    @9
    @1
    @12
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
    @14
    @15
    wceq
    @5
    @1
    @8
    @17
    adantr
    @8
    @18
    @5
    cX
    cY
    cV
    s2cl
    adantl
    @5
    @19
    @8
    @5
    @2
    @3
    cz
    wcel
    #
    @4
    @19
    @1
    @2
    @4
    simp2
    @1
    @2
    @20
    @4
    @1
    @3
    cV
    cW
    lencl
    nn0zd
    3ad2ant1
    @1
    @2
    @4
    simp3
    cI
    @3
    elfzo0z
    syl3anbrc
    adantr
    cV
    cW
    @12
    cI
    ccatval1
    syl3anc
    eqtrd
end
