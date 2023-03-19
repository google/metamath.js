include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cop.mm"
include "co.mm"
include "c1st.mm"
include "cfv.mm"
include "ccom.mm"
include "c2nd.mm"
include "cxp.mm"
include "wceq.mm"
include "simp1.mm"
include "opelxpi.mm"
include "3ad2ant2.mm"
include "3ad2ant3.mm"
include "dvhvadd.mm"
include "syl12anc.mm"
include "op1stg.mm"
include "coeq12d.mm"
include "op2ndg.mm"
include "oveq12d.mm"
include "opeq12d.mm"
include "eqtrd.mm"

theorem dvhopvadd
  let cD: class D
  let c.pl: class .+
  let c.pd: class .+^
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  let vf: setvar f
  let vg: setvar g
  assume dvhvadd.h: |- H = ( LHyp ` K )
  assume dvhvadd.t: |- T = ( ( LTrn ` K ) ` W )
  assume dvhvadd.e: |- E = ( ( TEndo ` K ) ` W )
  assume dvhvadd.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvhvadd.f: |- D = ( Scalar ` U )
  assume dvhvadd.s: |- .+ = ( +g ` U )
  assume dvhvadd.p: |- .+^ = ( +g ` D )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ Q e. E ) /\ ( G e. T /\ R e. E ) ) -> ( <. F , Q >. .+ <. G , R >. ) = <. ( F o. G ) , ( Q .+^ R ) >. )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cF
    cT
    wcel
    cQ
    cE
    wcel
    wa
    #
    cG
    cT
    wcel
    cR
    cE
    wcel
    wa
    #
    w3a
    #
    cF
    cQ
    cop
    #
    cG
    cR
    cop
    #
    c.pl
    co
    #
    @4
    c1st
    cfv
    #
    @5
    c1st
    cfv
    #
    ccom
    #
    @4
    c2nd
    cfv
    #
    @5
    c2nd
    cfv
    #
    c.pd
    co
    #
    cop
    #
    cF
    cG
    ccom
    #
    cQ
    cR
    c.pd
    co
    #
    cop
    @3
    @0
    @4
    cT
    cE
    cxp
    #
    wcel
    #
    @5
    @16
    wcel
    #
    @6
    @13
    wceq
    @0
    @1
    @2
    simp1
    @1
    @0
    @17
    @2
    cF
    cQ
    cT
    cE
    opelxpi
    3ad2ant2
    @2
    @0
    @18
    @1
    cG
    cR
    cT
    cE
    opelxpi
    3ad2ant3
    cD
    c.pl
    c.pd
    cT
    cU
    cE
    @4
    @5
    cH
    cK
    cW
    dvhvadd.h
    dvhvadd.t
    dvhvadd.e
    dvhvadd.u
    dvhvadd.f
    dvhvadd.s
    dvhvadd.p
    dvhvadd
    syl12anc
    @3
    @9
    @14
    @12
    @15
    @3
    @7
    cF
    @8
    cG
    @1
    @0
    @7
    cF
    wceq
    @2
    cF
    cQ
    cT
    cE
    op1stg
    3ad2ant2
    @2
    @0
    @8
    cG
    wceq
    @1
    cG
    cR
    cT
    cE
    op1stg
    3ad2ant3
    coeq12d
    @3
    @10
    cQ
    @11
    cR
    c.pd
    @1
    @0
    @10
    cQ
    wceq
    @2
    cF
    cQ
    cT
    cE
    op2ndg
    3ad2ant2
    @2
    @0
    @11
    cR
    wceq
    @1
    cG
    cR
    cT
    cE
    op2ndg
    3ad2ant3
    oveq12d
    opeq12d
    eqtrd
end
