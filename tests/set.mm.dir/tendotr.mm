include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "cid.mm"
include "cres.mm"
include "simpl1.mm"
include "simpl2l.mm"
include "tendoid.mm"
include "syl2anc.mm"
include "simpr.mm"
include "fveq2d.mm"
include "3eqtr4d.mm"
include "cple.mm"
include "wbr.mm"
include "simpl3.mm"
include "eqid.mm"
include "tendotp.mm"
include "syl3anc.mm"
include "cal.mm"
include "catm.mm"
include "wb.mm"
include "simpl1l.mm"
include "hlatl.mm"
include "syl.mm"
include "tendocl.mm"
include "simpl2r.mm"
include "tendoid0.mm"
include "syl112anc.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "trlnidat.mm"
include "atcmp.mm"
include "mpbid.mm"
include "pm2.61dane.mm"

theorem tendotr
  let cB: class B
  let cR: class R
  let cT: class T
  let cU: class U
  let vf: setvar f
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let cO: class O
  let cW: class W
  assume tendotr.b: |- B = ( Base ` K )
  assume tendotr.h: |- H = ( LHyp ` K )
  assume tendotr.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendotr.r: |- R = ( ( trL ` K ) ` W )
  assume tendotr.e: |- E = ( ( TEndo ` K ) ` W )
  assume tendotr.o: |- O = ( f e. T |-> ( _I |` B ) )

  disjoint B f
  disjoint T f
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( U e. E /\ U =/= O ) /\ F e. T ) -> ( R ` ( U ` F ) ) = ( R ` F ) )

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
    #
    cU
    cO
    wne
    #
    wa
    #
    cF
    cT
    wcel
    #
    w3a
    #
    cF
    cU
    cfv
    #
    cR
    cfv
    #
    cF
    cR
    cfv
    #
    wceq
    #
    cF
    cid
    cB
    cres
    #
    @7
    cF
    @12
    wceq
    #
    wa
    #
    @8
    cF
    cR
    @14
    @12
    cU
    cfv
    #
    @12
    @8
    cF
    @14
    @2
    @3
    @15
    @12
    wceq
    @2
    @5
    @6
    @13
    simpl1
    @3
    @4
    @2
    @6
    @13
    simpl2l
    cB
    cU
    cE
    cH
    cK
    cW
    tendotr.b
    tendotr.h
    tendotr.e
    tendoid
    syl2anc
    @14
    cF
    @12
    cU
    @7
    @13
    simpr
    #
    fveq2d
    @16
    3eqtr4d
    fveq2d
    @7
    cF
    @12
    wne
    #
    wa
    #
    @9
    @10
    cK
    cple
    cfv
    #
    wbr
    #
    @11
    @18
    @2
    @3
    @6
    @20
    @2
    @5
    @6
    @17
    simpl1
    #
    @3
    @4
    @2
    @6
    @17
    simpl2l
    #
    @2
    @5
    @6
    @17
    simpl3
    #
    cR
    cU
    cT
    cE
    cF
    cH
    cK
    @19
    chlt
    cW
    @19
    eqid
    #
    tendotr.h
    tendotr.t
    tendotr.r
    tendotr.e
    tendotp
    syl3anc
    @18
    cK
    cal
    wcel
    #
    @9
    cK
    catm
    cfv
    #
    wcel
    #
    @10
    @26
    wcel
    #
    @20
    @11
    wb
    @18
    @0
    @25
    @0
    @1
    @5
    @6
    @17
    simpl1l
    cK
    hlatl
    syl
    @18
    @2
    @8
    cT
    wcel
    #
    @8
    @12
    wne
    #
    @27
    @21
    @18
    @2
    @3
    @6
    @29
    @21
    @22
    @23
    cU
    cT
    cE
    cF
    cH
    cK
    chlt
    cW
    tendotr.h
    tendotr.t
    tendotr.e
    tendocl
    syl3anc
    @18
    @30
    @4
    @3
    @4
    @2
    @6
    @17
    simpl2r
    @18
    @8
    @12
    cU
    cO
    @18
    @2
    @3
    @6
    @17
    @8
    @12
    wceq
    cU
    cO
    wceq
    wb
    @21
    @22
    @23
    @7
    @17
    simpr
    #
    cB
    cT
    cU
    vf
    cE
    cF
    cH
    cK
    cO
    cW
    tendotr.b
    tendotr.h
    tendotr.t
    tendotr.e
    tendotr.o
    tendoid0
    syl112anc
    necon3bid
    mpbird
    @26
    cB
    cR
    cT
    @8
    cH
    cK
    cW
    tendotr.b
    @26
    eqid
    #
    tendotr.h
    tendotr.t
    tendotr.r
    trlnidat
    syl3anc
    @18
    @2
    @6
    @17
    @28
    @21
    @23
    @31
    @26
    cB
    cR
    cT
    cF
    cH
    cK
    cW
    tendotr.b
    @32
    tendotr.h
    tendotr.t
    tendotr.r
    trlnidat
    syl3anc
    @26
    @9
    @10
    cK
    @19
    @24
    @32
    atcmp
    syl3anc
    mpbid
    pm2.61dane
end
