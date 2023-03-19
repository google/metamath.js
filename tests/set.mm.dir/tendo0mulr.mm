include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "ccom.mm"
include "wceq.mm"
include "wrex.mm"
include "cdlemftr0.mm"
include "adantr.mm"
include "cfv.mm"
include "simpll.mm"
include "simplr.mm"
include "tendo0cl.mm"
include "ad2antrr.mm"
include "tendococl.mm"
include "syl3anc.mm"
include "tendo02.mm"
include "ad2antrl.mm"
include "fveq2d.mm"
include "tendoid.mm"
include "eqtrd.mm"
include "simprl.mm"
include "tendocoval.mm"
include "syl121anc.mm"
include "3eqtr4d.mm"
include "simpr.mm"
include "tendocan.mm"
include "syl131anc.mm"
include "rexlimddv.mm"

theorem tendo0mulr
  let cB: class B
  let cT: class T
  let cU: class U
  let vf: setvar f
  let cE: class E
  let cH: class H
  let cK: class K
  let cO: class O
  let cW: class W
  let vg: setvar g
  let cV: class V
  assume tendoid0.b: |- B = ( Base ` K )
  assume tendoid0.h: |- H = ( LHyp ` K )
  assume tendoid0.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendoid0.e: |- E = ( ( TEndo ` K ) ` W )
  assume tendoid0.o: |- O = ( f e. T |-> ( _I |` B ) )

  disjoint B f
  disjoint T f
  disjoint f g
  disjoint B g
  disjoint H g
  disjoint K g
  disjoint T g
  disjoint W g
  disjoint E g
  disjoint O g
  disjoint U g
  disjoint V g
  assert |- ( ( ( K e. HL /\ W e. H ) /\ U e. E ) -> ( U o. O ) = O )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cU
    cE
    wcel
    #
    wa
    #
    vg
    cv
    #
    cid
    cB
    cres
    #
    wne
    #
    cU
    cO
    ccom
    #
    cO
    wceq
    #
    vg
    cT
    @0
    @5
    vg
    cT
    wrex
    @1
    cB
    cT
    vg
    cH
    cK
    cW
    tendoid0.b
    tendoid0.h
    tendoid0.t
    cdlemftr0
    adantr
    @2
    @3
    cT
    wcel
    #
    @5
    wa
    #
    wa
    #
    @0
    @6
    cE
    wcel
    #
    cO
    cE
    wcel
    #
    @3
    @6
    cfv
    #
    @3
    cO
    cfv
    #
    wceq
    @9
    @7
    @0
    @1
    @9
    simpll
    #
    @10
    @0
    @1
    @12
    @11
    @15
    @0
    @1
    @9
    simplr
    #
    @0
    @12
    @1
    @9
    cB
    cT
    vf
    cE
    cH
    cK
    cO
    cW
    tendoid0.b
    tendoid0.h
    tendoid0.t
    tendoid0.e
    tendoid0.o
    tendo0cl
    ad2antrr
    #
    cU
    cO
    cE
    cH
    cK
    cW
    tendoid0.h
    tendoid0.e
    tendococl
    syl3anc
    @17
    @10
    @14
    cU
    cfv
    #
    @4
    @13
    @14
    @10
    @18
    @4
    cU
    cfv
    #
    @4
    @10
    @14
    @4
    cU
    @8
    @14
    @4
    wceq
    @2
    @5
    cB
    cT
    vf
    @3
    cK
    cO
    tendoid0.o
    tendoid0.b
    tendo02
    ad2antrl
    #
    fveq2d
    @2
    @19
    @4
    wceq
    @9
    cB
    cU
    cE
    cH
    cK
    cW
    tendoid0.b
    tendoid0.h
    tendoid0.e
    tendoid
    adantr
    eqtrd
    @10
    @0
    @1
    @12
    @8
    @13
    @18
    wceq
    @15
    @16
    @17
    @2
    @8
    @5
    simprl
    cT
    cU
    cE
    @3
    cH
    cK
    cO
    cW
    chlt
    tendoid0.h
    tendoid0.t
    tendoid0.e
    tendocoval
    syl121anc
    @20
    3eqtr4d
    @2
    @9
    simpr
    cB
    cT
    @6
    cE
    @3
    cH
    cK
    cO
    cW
    tendoid0.b
    tendoid0.h
    tendoid0.t
    tendoid0.e
    tendocan
    syl131anc
    rexlimddv
end
