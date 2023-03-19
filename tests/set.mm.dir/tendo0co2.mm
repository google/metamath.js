include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "ccom.mm"
include "cfv.mm"
include "cid.mm"
include "cres.mm"
include "wceq.mm"
include "ltrnco.mm"
include "tendo02.mm"
include "syl.mm"
include "3ad2ant2.mm"
include "3ad2ant3.mm"
include "coeq12d.mm"
include "wf1o.mm"
include "wf.mm"
include "f1oi.mm"
include "f1of.mm"
include "fcoi1.mm"
include "mp2b.mm"
include "syl6req.mm"
include "eqtrd.mm"

theorem tendo0co2
  let cB: class B
  let cT: class T
  let vf: setvar f
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cO: class O
  let cW: class W
  assume tendo0.b: |- B = ( Base ` K )
  assume tendo0.h: |- H = ( LHyp ` K )
  assume tendo0.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendo0.e: |- E = ( ( TEndo ` K ) ` W )
  assume tendo0.o: |- O = ( f e. T |-> ( _I |` B ) )

  disjoint B f
  disjoint T f
  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ G e. T ) -> ( O ` ( F o. G ) ) = ( ( O ` F ) o. ( O ` G ) ) )

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
    #
    cG
    cT
    wcel
    #
    w3a
    #
    cF
    cG
    ccom
    #
    cO
    cfv
    #
    cid
    cB
    cres
    #
    cF
    cO
    cfv
    #
    cG
    cO
    cfv
    #
    ccom
    #
    @3
    @4
    cT
    wcel
    @5
    @6
    wceq
    cT
    cF
    cG
    cH
    cK
    cW
    tendo0.h
    tendo0.t
    ltrnco
    cB
    cT
    vf
    @4
    cK
    cO
    tendo0.o
    tendo0.b
    tendo02
    syl
    @3
    @9
    @6
    @6
    ccom
    #
    @6
    @3
    @7
    @6
    @8
    @6
    @1
    @0
    @7
    @6
    wceq
    @2
    cB
    cT
    vf
    cF
    cK
    cO
    tendo0.o
    tendo0.b
    tendo02
    3ad2ant2
    @2
    @0
    @8
    @6
    wceq
    @1
    cB
    cT
    vf
    cG
    cK
    cO
    tendo0.o
    tendo0.b
    tendo02
    3ad2ant3
    coeq12d
    cB
    cB
    @6
    wf1o
    cB
    cB
    @6
    wf
    @10
    @6
    wceq
    cB
    f1oi
    cB
    cB
    @6
    f1of
    cB
    cB
    @6
    fcoi1
    mp2b
    syl6req
    eqtrd
end
