include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cfv.mm"
include "wss.mm"
include "w3a.mm"
include "crn.mm"
include "wceq.mm"
include "c0g.mm"
include "simpr.mm"
include "dihlsprn.mm"
include "3adant3.mm"
include "ad2antrr.mm"
include "eqeltrd.mm"
include "cp0.mm"
include "simpll1.mm"
include "eqid.mm"
include "dih0.mm"
include "syl.mm"
include "eqtr4d.mm"
include "cbs.mm"
include "wfn.mm"
include "dihfn.mm"
include "cops.mm"
include "simp1l.mm"
include "hlop.mm"
include "op0cl.mm"
include "3syl.mm"
include "fnfvelrn.mm"
include "syl2anc.mm"
include "clvec.mm"
include "wo.mm"
include "simpl1.mm"
include "dvhlvec.mm"
include "simpl2.mm"
include "simpl3.mm"
include "lspsnat.mm"
include "syl31anc.mm"
include "mpjaodan.mm"
include "ex.mm"
include "dihsslss.mm"
include "3ad2ant1.mm"
include "sseld.mm"
include "impbid.mm"

theorem dihlspsnssN
  let cS: class S
  let cT: class T
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  assume dih1dor0.h: |- H = ( LHyp ` K )
  assume dih1dor0.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihldor0.v: |- V = ( Base ` U )
  assume dih1dor0.s: |- S = ( LSubSp ` U )
  assume dih1dor0.n: |- N = ( LSpan ` U )
  assume dih1dor0.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X e. V /\ T C_ ( N ` { X } ) ) -> ( T e. S <-> T e. ran I ) )

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
    cX
    cV
    wcel
    #
    cT
    cX
    csn
    cN
    cfv
    #
    wss
    #
    w3a
    #
    cT
    cS
    wcel
    #
    cT
    cI
    crn
    #
    wcel
    #
    @6
    @7
    @9
    @6
    @7
    wa
    #
    cT
    @4
    wceq
    #
    @9
    cT
    cU
    c0g
    cfv
    #
    csn
    #
    wceq
    #
    @10
    @11
    wa
    cT
    @4
    @8
    @10
    @11
    simpr
    @6
    @4
    @8
    wcel
    #
    @7
    @11
    @2
    @3
    @15
    @5
    cU
    cH
    cI
    cK
    cN
    cV
    cW
    cX
    dih1dor0.h
    dih1dor0.u
    dihldor0.v
    dih1dor0.n
    dih1dor0.i
    dihlsprn
    3adant3
    ad2antrr
    eqeltrd
    @10
    @14
    wa
    #
    cT
    cK
    cp0
    cfv
    #
    cI
    cfv
    #
    @8
    @16
    cT
    @13
    @18
    @10
    @14
    simpr
    @16
    @2
    @18
    @13
    wceq
    @2
    @3
    @5
    @7
    @14
    simpll1
    #
    cU
    cH
    cI
    cK
    @12
    cW
    @17
    @17
    eqid
    #
    dih1dor0.h
    dih1dor0.i
    dih1dor0.u
    @12
    eqid
    #
    dih0
    syl
    eqtr4d
    @16
    cI
    cK
    cbs
    cfv
    #
    wfn
    #
    @17
    @22
    wcel
    #
    @18
    @8
    wcel
    @16
    @2
    @23
    @19
    @22
    cH
    cI
    cK
    cW
    @22
    eqid
    #
    dih1dor0.h
    dih1dor0.i
    dihfn
    syl
    @16
    @0
    cK
    cops
    wcel
    @24
    @6
    @0
    @7
    @14
    @0
    @1
    @3
    @5
    simp1l
    ad2antrr
    cK
    hlop
    @22
    cK
    @17
    @25
    @20
    op0cl
    3syl
    @22
    @17
    cI
    fnfvelrn
    syl2anc
    eqeltrd
    @10
    cU
    clvec
    wcel
    @7
    @3
    @5
    @11
    @14
    wo
    @10
    cU
    cH
    cK
    cW
    dih1dor0.h
    dih1dor0.u
    @2
    @3
    @5
    @7
    simpl1
    dvhlvec
    @6
    @7
    simpr
    @2
    @3
    @5
    @7
    simpl2
    @2
    @3
    @5
    @7
    simpl3
    cS
    cT
    cN
    cV
    cU
    cX
    @12
    dihldor0.v
    @21
    dih1dor0.s
    dih1dor0.n
    lspsnat
    syl31anc
    mpjaodan
    ex
    @6
    @8
    cS
    cT
    @2
    @3
    @8
    cS
    wss
    @5
    cS
    cU
    cH
    cI
    cK
    cW
    dih1dor0.h
    dih1dor0.u
    dih1dor0.i
    dih1dor0.s
    dihsslss
    3ad2ant1
    sseld
    impbid
end
