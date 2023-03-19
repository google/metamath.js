include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cop.mm"
include "co.mm"
include "ccom.mm"
include "csca.mm"
include "cfv.mm"
include "cplusg.mm"
include "eqid.mm"
include "dvhopvadd.mm"
include "wceq.mm"
include "dvhfplusr.mm"
include "3ad2ant1.mm"
include "oveqd.mm"
include "opeq2d.mm"
include "eqtrd.mm"

theorem dvhopvadd2
  let vt: setvar t
  let c.pl: class .+
  let c.pb: class .+b
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cU: class U
  let vf: setvar f
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  let vs: setvar s
  assume dvhopvadd2.h: |- H = ( LHyp ` K )
  assume dvhopvadd2.t: |- T = ( ( LTrn ` K ) ` W )
  assume dvhopvadd2.e: |- E = ( ( TEndo ` K ) ` W )
  assume dvhopvadd2.p: |- .+ = ( s e. E , t e. E |-> ( f e. T |-> ( ( s ` f ) o. ( t ` f ) ) ) )
  assume dvhopvadd2.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvhopvadd2.s: |- .+b = ( +g ` U )

  disjoint s t
  disjoint E s
  disjoint E t
  disjoint H f
  disjoint f s
  disjoint f t
  disjoint K f
  disjoint K s
  disjoint K t
  disjoint W f
  disjoint W s
  disjoint W t
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ Q e. E ) /\ ( G e. T /\ R e. E ) ) -> ( <. F , Q >. .+b <. G , R >. ) = <. ( F o. G ) , ( Q .+ R ) >. )

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
    cG
    cR
    cop
    c.pb
    co
    cF
    cG
    ccom
    #
    cQ
    cR
    cU
    csca
    cfv
    #
    cplusg
    cfv
    #
    co
    #
    cop
    @4
    cQ
    cR
    c.pl
    co
    #
    cop
    @5
    c.pb
    @6
    cQ
    cR
    cT
    cU
    cE
    cF
    cG
    cH
    cK
    cW
    dvhopvadd2.h
    dvhopvadd2.t
    dvhopvadd2.e
    dvhopvadd2.u
    @5
    eqid
    #
    dvhopvadd2.s
    @6
    eqid
    #
    dvhopvadd
    @3
    @7
    @8
    @4
    @3
    @6
    c.pl
    cQ
    cR
    @0
    @1
    @6
    c.pl
    wceq
    @2
    vt
    c.pl
    @6
    cT
    cU
    vf
    cE
    @5
    cH
    cK
    chlt
    cW
    vs
    dvhopvadd2.h
    dvhopvadd2.t
    dvhopvadd2.e
    dvhopvadd2.u
    @9
    dvhopvadd2.p
    @10
    dvhfplusr
    3ad2ant1
    oveqd
    opeq2d
    eqtrd
end
