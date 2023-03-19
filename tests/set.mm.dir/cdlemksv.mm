include "cv.mm"
include "cfv.mm"
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "wceq.mm"
include "crio.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "coeq1.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "eqeq2d.mm"
include "riotabidv.mm"
include "riotaex.mm"
include "fvmpt.mm"

theorem cdlemksv
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
  assume cdlemk.b: |- B = ( Base ` K )
  assume cdlemk.l: |- .<_ = ( le ` K )
  assume cdlemk.j: |- .\/ = ( join ` K )
  assume cdlemk.a: |- A = ( Atoms ` K )
  assume cdlemk.h: |- H = ( LHyp ` K )
  assume cdlemk.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk.m: |- ./\ = ( meet ` K )
  assume cdlemk.s: |- S = ( f e. T |-> ( iota_ i e. T ( i ` P ) = ( ( P .\/ ( R ` f ) ) ./\ ( ( N ` P ) .\/ ( R ` ( f o. `' F ) ) ) ) ) )

  disjoint ./\ f
  disjoint .\/ f
  disjoint F f
  disjoint f i
  disjoint G f
  disjoint G i
  disjoint N f
  disjoint P f
  disjoint R f
  disjoint T f
  disjoint W f
  assert |- ( G e. T -> ( S ` G ) = ( iota_ i e. T ( i ` P ) = ( ( P .\/ ( R ` G ) ) ./\ ( ( N ` P ) .\/ ( R ` ( G o. `' F ) ) ) ) ) )

  proof
    vf
    cG
    cP
    vi
    cv
    cfv
    #
    cP
    vf
    cv
    #
    cR
    cfv
    #
    c.or
    co
    #
    cP
    cN
    cfv
    #
    @1
    cF
    ccnv
    #
    ccom
    #
    cR
    cfv
    #
    c.or
    co
    #
    c.an
    co
    #
    wceq
    #
    vi
    cT
    crio
    @0
    cP
    cG
    cR
    cfv
    #
    c.or
    co
    #
    @4
    cG
    @5
    ccom
    #
    cR
    cfv
    #
    c.or
    co
    #
    c.an
    co
    #
    wceq
    #
    vi
    cT
    crio
    cT
    cS
    @1
    cG
    wceq
    #
    @10
    @17
    vi
    cT
    @18
    @9
    @16
    @0
    @18
    @3
    @12
    @8
    @15
    c.an
    @18
    @2
    @11
    cP
    c.or
    @1
    cG
    cR
    fveq2
    oveq2d
    @18
    @7
    @14
    @4
    c.or
    @18
    @6
    @13
    cR
    @1
    cG
    @5
    coeq1
    fveq2d
    oveq2d
    oveq12d
    eqeq2d
    riotabidv
    cdlemk.s
    @17
    vi
    cT
    riotaex
    fvmpt
end
