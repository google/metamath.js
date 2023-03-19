include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cid.mm"
include "cres.mm"
include "wceq.mm"
include "cfv.mm"
include "ltrniotaval.mm"
include "3anidm23.mm"
include "wb.mm"
include "simpl.mm"
include "ltrniotacl.mm"
include "simpr.mm"
include "ltrnideq.mm"
include "syl3anc.mm"
include "mpbird.mm"

theorem ltrniotaidvalN
  let cA: class A
  let cB: class B
  let cP: class P
  let cT: class T
  let vf: setvar f
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume ltrniotaidval.b: |- B = ( Base ` K )
  assume ltrniotaidval.l: |- .<_ = ( le ` K )
  assume ltrniotaidval.a: |- A = ( Atoms ` K )
  assume ltrniotaidval.h: |- H = ( LHyp ` K )
  assume ltrniotaidval.t: |- T = ( ( LTrn ` K ) ` W )
  assume ltrniotaidval.f: |- F = ( iota_ f e. T ( f ` P ) = P )

  disjoint .<_ f
  disjoint A f
  disjoint H f
  disjoint K f
  disjoint P f
  disjoint T f
  disjoint W f
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) ) -> F = ( _I |` B ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    #
    wa
    #
    cF
    cid
    cB
    cres
    wceq
    #
    cP
    cF
    cfv
    cP
    wceq
    #
    @0
    @1
    @4
    cA
    cP
    cP
    cT
    vf
    cF
    cH
    cK
    c.le
    cW
    ltrniotaidval.l
    ltrniotaidval.a
    ltrniotaidval.h
    ltrniotaidval.t
    ltrniotaidval.f
    ltrniotaval
    3anidm23
    @2
    @0
    cF
    cT
    wcel
    #
    @1
    @3
    @4
    wb
    @0
    @1
    simpl
    @0
    @1
    @5
    cA
    cP
    cP
    cT
    vf
    cF
    cH
    cK
    c.le
    cW
    ltrniotaidval.l
    ltrniotaidval.a
    ltrniotaidval.h
    ltrniotaidval.t
    ltrniotaidval.f
    ltrniotacl
    3anidm23
    @0
    @1
    simpr
    cA
    cB
    cP
    cT
    cF
    cH
    cK
    c.le
    cW
    ltrniotaidval.b
    ltrniotaidval.l
    ltrniotaidval.a
    ltrniotaidval.h
    ltrniotaidval.t
    ltrnideq
    syl3anc
    mpbird
end
