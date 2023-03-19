include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cp0.mm"
include "cid.mm"
include "cres.mm"
include "wceq.mm"
include "tendo02.mm"
include "adantl.mm"
include "fveq2d.mm"
include "eqid.mm"
include "trlid0.mm"
include "adantr.mm"
include "eqtrd.mm"
include "cops.mm"
include "wbr.mm"
include "hlop.mm"
include "ad2antrr.mm"
include "trlcl.mm"
include "op0le.mm"
include "syl2anc.mm"
include "eqbrtrd.mm"

theorem tendo0tp
  let cB: class B
  let cR: class R
  let cT: class T
  let vf: setvar f
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cO: class O
  let cW: class W
  assume tendo0.b: |- B = ( Base ` K )
  assume tendo0.h: |- H = ( LHyp ` K )
  assume tendo0.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendo0.e: |- E = ( ( TEndo ` K ) ` W )
  assume tendo0.o: |- O = ( f e. T |-> ( _I |` B ) )
  assume tendo0tp.l: |- .<_ = ( le ` K )
  assume tendo0tp.r: |- R = ( ( trL ` K ) ` W )

  disjoint B f
  disjoint T f
  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T ) -> ( R ` ( O ` F ) ) .<_ ( R ` F ) )

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
    cF
    cT
    wcel
    #
    wa
    #
    cF
    cO
    cfv
    #
    cR
    cfv
    #
    cK
    cp0
    cfv
    #
    cF
    cR
    cfv
    #
    c.le
    @4
    @6
    cid
    cB
    cres
    #
    cR
    cfv
    #
    @7
    @4
    @5
    @9
    cR
    @3
    @5
    @9
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
    adantl
    fveq2d
    @2
    @10
    @7
    wceq
    @3
    cB
    cR
    cH
    cK
    cW
    @7
    tendo0.b
    @7
    eqid
    #
    tendo0.h
    tendo0tp.r
    trlid0
    adantr
    eqtrd
    @4
    cK
    cops
    wcel
    #
    @8
    cB
    wcel
    @7
    @8
    c.le
    wbr
    @0
    @12
    @1
    @3
    cK
    hlop
    ad2antrr
    cB
    cR
    cT
    cF
    cH
    cK
    cW
    tendo0.b
    tendo0.h
    tendo0.t
    tendo0tp.r
    trlcl
    cB
    cK
    c.le
    @8
    @7
    tendo0.b
    tendo0tp.l
    @11
    op0le
    syl2anc
    eqbrtrd
end
