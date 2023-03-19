include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
include "cfv.mm"
include "cbs.mm"
include "cdr.mm"
include "c0g.mm"
include "cedring.mm"
include "eqid.mm"
include "dvhsca.mm"
include "erngdv.mm"
include "eqeltrd.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "wceq.mm"
include "dvhbase.mm"
include "eleqtrrd.mm"
include "simp3.mm"
include "fveq2d.mm"
include "erng0g.mm"
include "eqtrd.mm"
include "neeqtrrd.mm"
include "drnginvrcl.mm"
include "syl3anc.mm"
include "eleqtrd.mm"
include "drnginvrn0.mm"
include "neeqtrd.mm"
include "jca.mm"

theorem tendoinvcl
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ S e. E /\ S =/= O ) -> ( ( N ` S ) e. E /\ ( N ` S ) =/= O ) )

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
    cN
    cfv
    #
    cE
    wcel
    @4
    cO
    wne
    @3
    @4
    cF
    cbs
    cfv
    #
    cE
    @3
    cF
    cdr
    wcel
    #
    cS
    @5
    wcel
    #
    cS
    cF
    c0g
    cfv
    #
    wne
    #
    @4
    @5
    wcel
    @0
    @1
    @6
    @2
    @0
    cF
    cW
    cK
    cedring
    cfv
    cfv
    #
    cdr
    @10
    cU
    cF
    cH
    cK
    cW
    chlt
    tendoinv.h
    @10
    eqid
    #
    tendoinv.u
    tendoinv.f
    dvhsca
    #
    @10
    cH
    cK
    cW
    tendoinv.h
    @11
    erngdv
    eqeltrd
    3ad2ant1
    #
    @3
    cS
    cE
    @5
    @0
    @1
    @2
    simp2
    @0
    @1
    @5
    cE
    wceq
    @2
    @5
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
    @5
    eqid
    #
    dvhbase
    3ad2ant1
    #
    eleqtrrd
    #
    @3
    cS
    cO
    @8
    @0
    @1
    @2
    simp3
    @0
    @1
    @8
    cO
    wceq
    @2
    @0
    @8
    @10
    c0g
    cfv
    #
    cO
    @0
    cF
    @10
    c0g
    @12
    fveq2d
    cB
    @10
    cT
    vh
    cH
    cK
    cO
    cW
    @17
    tendoinv.b
    tendoinv.h
    tendoinv.t
    @11
    tendoinv.o
    @17
    eqid
    erng0g
    eqtrd
    3ad2ant1
    #
    neeqtrrd
    #
    @5
    cF
    cN
    cS
    @8
    @14
    @8
    eqid
    #
    tendoinv.n
    drnginvrcl
    syl3anc
    @15
    eleqtrd
    @3
    @4
    @8
    cO
    @3
    @6
    @7
    @9
    @4
    @8
    wne
    @13
    @16
    @19
    @5
    cF
    cN
    cS
    @8
    @14
    @20
    tendoinv.n
    drnginvrn0
    syl3anc
    @18
    neeqtrd
    jca
end
