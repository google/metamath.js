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
include "tendo0cl.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "tendococl.mm"
include "syl3anc.mm"
include "simprl.mm"
include "tendocl.mm"
include "tendo02.mm"
include "syl.mm"
include "tendocoval.mm"
include "syl121anc.mm"
include "ad2antrl.mm"
include "3eqtr4d.mm"
include "simpr.mm"
include "tendocan.mm"
include "syl131anc.mm"
include "rexlimddv.mm"

theorem tendo0mul
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ U e. E ) -> ( O o. U ) = O )

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
    cO
    cU
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
    @12
    @1
    @11
    @15
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
    @0
    @1
    @9
    simplr
    #
    cO
    cU
    cE
    cH
    cK
    cW
    tendoid0.h
    tendoid0.e
    tendococl
    syl3anc
    @16
    @10
    @3
    cU
    cfv
    #
    cO
    cfv
    #
    @4
    @13
    @14
    @10
    @18
    cT
    wcel
    #
    @19
    @4
    wceq
    @10
    @0
    @1
    @8
    @20
    @15
    @17
    @2
    @8
    @5
    simprl
    #
    cU
    cT
    cE
    @3
    cH
    cK
    chlt
    cW
    tendoid0.h
    tendoid0.t
    tendoid0.e
    tendocl
    syl3anc
    cB
    cT
    vf
    @18
    cK
    cO
    tendoid0.o
    tendoid0.b
    tendo02
    syl
    @10
    @0
    @12
    @1
    @8
    @13
    @19
    wceq
    @15
    @16
    @17
    @21
    cT
    cO
    cE
    @3
    cH
    cK
    cU
    cW
    chlt
    tendoid0.h
    tendoid0.t
    tendoid0.e
    tendocoval
    syl121anc
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
