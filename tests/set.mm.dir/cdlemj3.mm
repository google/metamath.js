include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "catm.mm"
include "wrex.mm"
include "simpl1.mm"
include "eqid.mm"
include "lhpexle2.mm"
include "syl.mm"
include "simpl1l.mm"
include "adantr.mm"
include "simpl1r.mm"
include "simprl.mm"
include "simprr1.mm"
include "cdlemfnid.mm"
include "syl22anc.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp3l.mm"
include "simp3rr.mm"
include "simp2r2.mm"
include "necomd.mm"
include "simp3rl.mm"
include "neeqtrrd.mm"
include "simp2r3.mm"
include "eqnetrd.mm"
include "cdlemj2.mm"
include "syl132anc.mm"
include "3expia.mm"
include "expd.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "rexlimddv.mm"

theorem cdlemj3
  let cB: class B
  let cR: class R
  let cT: class T
  let cU: class U
  let vh: setvar h
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vp: setvar p
  let vg: setvar g
  let vu: setvar u
  assume cdlemj.b: |- B = ( Base ` K )
  assume cdlemj.h: |- H = ( LHyp ` K )
  assume cdlemj.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemj.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemj.e: |- E = ( ( TEndo ` K ) ` W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( U e. E /\ V e. E /\ ( U ` F ) = ( V ` F ) ) /\ ( F e. T /\ F =/= ( _I |` B ) /\ h e. T ) ) /\ h =/= ( _I |` B ) ) -> ( U ` h ) = ( V ` h ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cU
    cE
    wcel
    cV
    cE
    wcel
    cF
    cU
    cfv
    cF
    cV
    cfv
    wceq
    w3a
    #
    cF
    cT
    wcel
    cF
    cid
    cB
    cres
    #
    wne
    vh
    cv
    #
    cT
    wcel
    w3a
    #
    w3a
    #
    @5
    @4
    wne
    #
    wa
    #
    vu
    cv
    #
    cW
    cK
    cple
    cfv
    #
    wbr
    #
    @10
    cF
    cR
    cfv
    #
    wne
    #
    @10
    @5
    cR
    cfv
    #
    wne
    #
    w3a
    #
    @5
    cU
    cfv
    @5
    cV
    cfv
    wceq
    #
    vu
    cK
    catm
    cfv
    #
    @9
    @2
    @17
    vu
    @19
    wrex
    @2
    @3
    @6
    @8
    simpl1
    @19
    cH
    cK
    @11
    cW
    @13
    @15
    vu
    @11
    eqid
    #
    @19
    eqid
    #
    cdlemj.h
    lhpexle2
    syl
    @9
    @10
    @19
    wcel
    #
    @17
    wa
    #
    wa
    #
    vg
    cv
    #
    cR
    cfv
    #
    @10
    wceq
    #
    @25
    @4
    wne
    #
    wa
    #
    vg
    cT
    wrex
    #
    @18
    @24
    @0
    @1
    @22
    @12
    @30
    @9
    @0
    @23
    @0
    @1
    @3
    @6
    @8
    simpl1l
    adantr
    @9
    @1
    @23
    @0
    @1
    @3
    @6
    @8
    simpl1r
    adantr
    @9
    @22
    @17
    simprl
    @12
    @14
    @16
    @22
    @9
    simprr1
    @19
    cB
    cR
    cT
    @10
    vg
    cH
    cK
    @11
    cW
    cdlemj.b
    @20
    @21
    cdlemj.h
    cdlemj.t
    cdlemj.r
    cdlemfnid
    syl22anc
    @24
    @29
    @18
    vg
    cT
    @24
    @25
    cT
    wcel
    #
    @29
    @18
    @9
    @23
    @31
    @29
    wa
    #
    @18
    @9
    @23
    @32
    w3a
    #
    @7
    @8
    @31
    @28
    @13
    @26
    wne
    @26
    @15
    wne
    @18
    @7
    @8
    @23
    @32
    simp1l
    @7
    @8
    @23
    @32
    simp1r
    @9
    @23
    @31
    @29
    simp3l
    @27
    @28
    @31
    @9
    @23
    simp3rr
    @33
    @13
    @10
    @26
    @33
    @10
    @13
    @12
    @14
    @16
    @22
    @9
    @32
    simp2r2
    necomd
    @27
    @28
    @31
    @9
    @23
    simp3rl
    #
    neeqtrrd
    @33
    @26
    @10
    @15
    @34
    @12
    @14
    @16
    @22
    @9
    @32
    simp2r3
    eqnetrd
    cB
    cR
    cT
    cU
    vg
    vh
    cE
    cF
    cH
    cK
    cV
    cW
    cdlemj.b
    cdlemj.h
    cdlemj.t
    cdlemj.r
    cdlemj.e
    cdlemj2
    syl132anc
    3expia
    expd
    rexlimdv
    mpd
    rexlimddv
end
