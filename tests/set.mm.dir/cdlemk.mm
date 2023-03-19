include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "cid.mm"
include "cbs.mm"
include "cres.mm"
include "wne.mm"
include "coc.mm"
include "cjn.mm"
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "cmee.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "cif.mm"
include "cmpt.mm"
include "wrex.mm"
include "catm.mm"
include "eqid.mm"
include "cdlemk56w.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "syl.mm"

theorem cdlemk
  let vu: setvar u
  let cR: class R
  let cT: class T
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let cN: class N
  let cW: class W
  let vb: setvar b
  let vf: setvar f
  let vz: setvar z
  assume cdlemk7.h: |- H = ( LHyp ` K )
  assume cdlemk7.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk7.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk7.e: |- E = ( ( TEndo ` K ) ` W )

  disjoint E u
  disjoint F u
  disjoint K u
  disjoint N u
  disjoint R u
  disjoint T u
  disjoint W u
  disjoint b f
  disjoint b u
  disjoint b z
  disjoint F b
  disjoint f u
  disjoint f z
  disjoint F f
  disjoint u z
  disjoint F z
  disjoint H b
  disjoint H f
  disjoint H z
  disjoint K b
  disjoint K f
  disjoint K z
  disjoint N b
  disjoint N f
  disjoint N z
  disjoint R b
  disjoint R f
  disjoint R z
  disjoint T b
  disjoint T f
  disjoint T z
  disjoint W b
  disjoint W f
  disjoint W z
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ N e. T ) /\ ( R ` F ) = ( R ` N ) ) -> E. u e. E ( u ` F ) = N )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cF
    cT
    wcel
    cN
    cT
    wcel
    wa
    cF
    cR
    cfv
    #
    cN
    cR
    cfv
    wceq
    w3a
    vf
    cT
    cF
    cN
    wceq
    vf
    cv
    #
    vb
    cv
    #
    cid
    cK
    cbs
    cfv
    #
    cres
    wne
    @2
    cR
    cfv
    #
    @0
    wne
    @4
    @1
    cR
    cfv
    #
    wne
    w3a
    cW
    cK
    coc
    cfv
    #
    cfv
    #
    vz
    cv
    cfv
    @7
    @5
    cK
    cjn
    cfv
    #
    co
    @7
    @4
    @8
    co
    @7
    cN
    cfv
    @2
    cF
    ccnv
    ccom
    cR
    cfv
    @8
    co
    cK
    cmee
    cfv
    #
    co
    #
    @1
    @2
    ccnv
    ccom
    cR
    cfv
    @8
    co
    @9
    co
    #
    wceq
    wi
    vb
    cT
    wral
    vz
    cT
    crio
    #
    cif
    cmpt
    #
    cE
    wcel
    cF
    @13
    cfv
    #
    cN
    wceq
    #
    wa
    cF
    vu
    cv
    #
    cfv
    #
    cN
    wceq
    #
    vu
    cE
    wrex
    vz
    cK
    catm
    cfv
    #
    @3
    @7
    cR
    cT
    @13
    vf
    cE
    cF
    cH
    @8
    cK
    @9
    cN
    @6
    cW
    @12
    @11
    @10
    vb
    @3
    eqid
    @8
    eqid
    @9
    eqid
    @6
    eqid
    @19
    eqid
    cdlemk7.h
    cdlemk7.t
    cdlemk7.r
    @7
    eqid
    @10
    eqid
    @11
    eqid
    @12
    eqid
    @13
    eqid
    cdlemk7.e
    cdlemk56w
    @18
    @15
    vu
    @13
    cE
    @16
    @13
    wceq
    @17
    @14
    cN
    cF
    @16
    @13
    fveq1
    eqeq1d
    rspcev
    syl
end
