include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cfv.mm"
include "crn.mm"
include "c0g.mm"
include "wceq.mm"
include "simpr.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "clmod.mm"
include "simpll.mm"
include "dvhlmod.mm"
include "eqid.mm"
include "lspsn0.mm"
include "syl.mm"
include "eqtrd.mm"
include "dih0rn.mm"
include "ad2antrr.mm"
include "eqeltrd.mm"
include "wne.mm"
include "clsa.mm"
include "simplr.mm"
include "lsatlspsn2.mm"
include "syl3anc.mm"
include "dih1dimat.mm"
include "syl2anc.mm"
include "pm2.61dane.mm"

theorem dihlsprn
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  assume dihlsprn.h: |- H = ( LHyp ` K )
  assume dihlsprn.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihlsprn.v: |- V = ( Base ` U )
  assume dihlsprn.n: |- N = ( LSpan ` U )
  assume dihlsprn.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X e. V ) -> ( N ` { X } ) e. ran I )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cV
    wcel
    #
    wa
    #
    cX
    csn
    #
    cN
    cfv
    #
    cI
    crn
    #
    wcel
    #
    cX
    cU
    c0g
    cfv
    #
    @2
    cX
    @7
    wceq
    #
    wa
    #
    @4
    @7
    csn
    #
    @5
    @9
    @4
    @10
    cN
    cfv
    #
    @10
    @9
    @3
    @10
    cN
    @9
    cX
    @7
    @2
    @8
    simpr
    sneqd
    fveq2d
    @9
    cU
    clmod
    wcel
    #
    @11
    @10
    wceq
    @9
    cU
    cH
    cK
    cW
    dihlsprn.h
    dihlsprn.u
    @0
    @1
    @8
    simpll
    dvhlmod
    cN
    cU
    @7
    @7
    eqid
    #
    dihlsprn.n
    lspsn0
    syl
    eqtrd
    @0
    @10
    @5
    wcel
    @1
    @8
    cU
    cH
    cI
    cK
    cW
    @7
    dihlsprn.h
    dihlsprn.i
    dihlsprn.u
    @13
    dih0rn
    ad2antrr
    eqeltrd
    @2
    cX
    @7
    wne
    #
    wa
    #
    @0
    @4
    cU
    clsa
    cfv
    #
    wcel
    #
    @6
    @0
    @1
    @14
    simpll
    #
    @15
    @12
    @1
    @14
    @17
    @15
    cU
    cH
    cK
    cW
    dihlsprn.h
    dihlsprn.u
    @18
    dvhlmod
    @0
    @1
    @14
    simplr
    @2
    @14
    simpr
    @16
    cN
    cV
    cU
    cX
    @7
    dihlsprn.v
    dihlsprn.n
    @13
    @16
    eqid
    #
    lsatlspsn2
    syl3anc
    @16
    @4
    cU
    cH
    cI
    cK
    cW
    dihlsprn.h
    dihlsprn.u
    dihlsprn.i
    @19
    dih1dimat
    syl2anc
    pm2.61dane
end
