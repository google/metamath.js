include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cdib.mm"
include "cop.mm"
include "csn.mm"
include "cple.mm"
include "wbr.mm"
include "wceq.mm"
include "simpl.mm"
include "trlcl.mm"
include "eqid.mm"
include "trlle.mm"
include "dihvalb.mm"
include "syl12anc.mm"
include "dib1dim2.mm"
include "eqtrd.mm"

theorem dih1dimb
  let cB: class B
  let cR: class R
  let cT: class T
  let cU: class U
  let vh: setvar h
  let cF: class F
  let cH: class H
  let cI: class I
  let cK: class K
  let cN: class N
  let cO: class O
  let cW: class W
  assume dih1dimb.b: |- B = ( Base ` K )
  assume dih1dimb.h: |- H = ( LHyp ` K )
  assume dih1dimb.t: |- T = ( ( LTrn ` K ) ` W )
  assume dih1dimb.r: |- R = ( ( trL ` K ) ` W )
  assume dih1dimb.o: |- O = ( h e. T |-> ( _I |` B ) )
  assume dih1dimb.u: |- U = ( ( DVecH ` K ) ` W )
  assume dih1dimb.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dih1dimb.n: |- N = ( LSpan ` U )

  disjoint B h
  disjoint K h
  disjoint T h
  disjoint W h
  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T ) -> ( I ` ( R ` F ) ) = ( N ` { <. F , O >. } ) )

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
    wa
    #
    cF
    cR
    cfv
    #
    cI
    cfv
    #
    @3
    cW
    cK
    cdib
    cfv
    cfv
    #
    cfv
    #
    cF
    cO
    cop
    csn
    cN
    cfv
    @2
    @0
    @3
    cB
    wcel
    @3
    cW
    cK
    cple
    cfv
    #
    wbr
    @4
    @6
    wceq
    @0
    @1
    simpl
    cB
    cR
    cT
    cF
    cH
    cK
    cW
    dih1dimb.b
    dih1dimb.h
    dih1dimb.t
    dih1dimb.r
    trlcl
    cR
    cT
    cF
    cH
    cK
    @7
    cW
    @7
    eqid
    #
    dih1dimb.h
    dih1dimb.t
    dih1dimb.r
    trlle
    cB
    @5
    cH
    cI
    cK
    @7
    chlt
    cW
    @3
    dih1dimb.b
    @8
    dih1dimb.h
    dih1dimb.i
    @5
    eqid
    #
    dihvalb
    syl12anc
    cB
    cR
    cT
    cU
    vh
    cF
    cH
    @5
    cK
    cN
    cO
    cW
    dih1dimb.b
    dih1dimb.h
    dih1dimb.t
    dih1dimb.r
    dih1dimb.o
    dih1dimb.u
    @9
    dih1dimb.n
    dib1dim2
    eqtrd
end
