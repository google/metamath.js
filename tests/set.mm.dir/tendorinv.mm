include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
include "cfv.mm"
include "cmulr.mm"
include "co.mm"
include "cur.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "cdr.mm"
include "cbs.mm"
include "c0g.mm"
include "wceq.mm"
include "cedring.mm"
include "simp1.mm"
include "eqid.mm"
include "dvhsca.mm"
include "syl.mm"
include "erngdv.mm"
include "eqeltrd.mm"
include "simp2.mm"
include "dvhbase.mm"
include "eleqtrrd.mm"
include "simp3.mm"
include "fveq2d.mm"
include "erng0g.mm"
include "eqtrd.mm"
include "neeqtrrd.mm"
include "drnginvrr.mm"
include "syl3anc.mm"
include "tendoinvcl.mm"
include "simpld.mm"
include "dvhmulr.mm"
include "syl12anc.mm"
include "erng1r.mm"
include "3eqtr3d.mm"

theorem tendorinv
  let cB: class B
  let cS: class S
  let cT: class T
  let cU: class U
  let vh: setvar h
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let cN: class N
  let cO: class O
  let cW: class W
  assume tendoinv.b: |- B = ( Base ` K )
  assume tendoinv.h: |- H = ( LHyp ` K )
  assume tendoinv.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendoinv.e: |- E = ( ( TEndo ` K ) ` W )
  assume tendoinv.o: |- O = ( h e. T |-> ( _I |` B ) )
  assume tendoinv.u: |- U = ( ( DVecH ` K ) ` W )
  assume tendoinv.f: |- F = ( Scalar ` U )
  assume tendoinv.n: |- N = ( invr ` F )

  disjoint B h
  disjoint H h
  disjoint K h
  disjoint T h
  disjoint W h
  assert |- ( ( ( K e. HL /\ W e. H ) /\ S e. E /\ S =/= O ) -> ( S o. ( N ` S ) ) = ( _I |` T ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cS
    cE
    wcel
    #
    cS
    cO
    wne
    #
    w3a
    #
    cS
    cS
    cN
    cfv
    #
    cF
    cmulr
    cfv
    #
    co
    #
    cF
    cur
    cfv
    #
    cS
    @4
    ccom
    #
    cid
    cT
    cres
    #
    @3
    cF
    cdr
    wcel
    cS
    cF
    cbs
    cfv
    #
    wcel
    cS
    cF
    c0g
    cfv
    #
    wne
    @6
    @7
    wceq
    @3
    cF
    cW
    cK
    cedring
    cfv
    cfv
    #
    cdr
    @3
    @0
    cF
    @12
    wceq
    @0
    @1
    @2
    simp1
    #
    @12
    cU
    cF
    cH
    cK
    cW
    chlt
    tendoinv.h
    @12
    eqid
    #
    tendoinv.u
    tendoinv.f
    dvhsca
    #
    syl
    @3
    @0
    @12
    cdr
    wcel
    @13
    @12
    cH
    cK
    cW
    tendoinv.h
    @14
    erngdv
    syl
    eqeltrd
    @3
    cS
    cE
    @10
    @0
    @1
    @2
    simp2
    #
    @3
    @0
    @10
    cE
    wceq
    @13
    @10
    cU
    cE
    cF
    cH
    cK
    cW
    chlt
    tendoinv.h
    tendoinv.e
    tendoinv.u
    tendoinv.f
    @10
    eqid
    #
    dvhbase
    syl
    eleqtrrd
    @3
    cS
    cO
    @11
    @0
    @1
    @2
    simp3
    @3
    @0
    @11
    cO
    wceq
    @13
    @0
    @11
    @12
    c0g
    cfv
    #
    cO
    @0
    cF
    @12
    c0g
    @15
    fveq2d
    cB
    @12
    cT
    vh
    cH
    cK
    cO
    cW
    @18
    tendoinv.b
    tendoinv.h
    tendoinv.t
    @14
    tendoinv.o
    @18
    eqid
    erng0g
    eqtrd
    syl
    neeqtrrd
    @10
    cF
    @5
    @7
    cN
    cS
    @11
    @17
    @11
    eqid
    @5
    eqid
    #
    @7
    eqid
    tendoinv.n
    drnginvrr
    syl3anc
    @3
    @0
    @1
    @4
    cE
    wcel
    #
    @6
    @8
    wceq
    @13
    @16
    @3
    @20
    @4
    cO
    wne
    cB
    cS
    cT
    cU
    vh
    cE
    cF
    cH
    cK
    cN
    cO
    cW
    tendoinv.b
    tendoinv.h
    tendoinv.t
    tendoinv.e
    tendoinv.o
    tendoinv.u
    tendoinv.f
    tendoinv.n
    tendoinvcl
    simpld
    cS
    @4
    cT
    @5
    cU
    cE
    cF
    cH
    cK
    chlt
    cW
    tendoinv.h
    tendoinv.t
    tendoinv.e
    tendoinv.u
    tendoinv.f
    @19
    dvhmulr
    syl12anc
    @3
    @0
    @7
    @9
    wceq
    @13
    @0
    @7
    @12
    cur
    cfv
    #
    @9
    @0
    cF
    @12
    cur
    @15
    fveq2d
    @12
    cT
    @21
    cH
    cK
    cW
    tendoinv.h
    tendoinv.t
    @14
    @21
    eqid
    erng1r
    eqtrd
    syl
    3eqtr3d
end
