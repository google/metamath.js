include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "csb.mm"
include "nfcvd.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "id.mm"
include "eqeq12d.mm"
include "anbi2d.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "riotabidv.mm"
include "csbiegf.mm"
include "csbeq2i.mm"
include "3eqtr4g.mm"

theorem cdleme31so
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let c.or: class .\/
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cW: class W
  let cX: class X
  let vs: setvar s
  assume cdleme31so.o: |- O = ( iota_ z e. B A. s e. A ( ( -. s .<_ W /\ ( s .\/ ( x ./\ W ) ) = x ) -> z = ( N .\/ ( x ./\ W ) ) ) )
  assume cdleme31so.c: |- C = ( iota_ z e. B A. s e. A ( ( -. s .<_ W /\ ( s .\/ ( X ./\ W ) ) = X ) -> z = ( N .\/ ( X ./\ W ) ) ) )

  disjoint A x
  disjoint B x
  disjoint .\/ x
  disjoint .<_ x
  disjoint ./\ x
  disjoint N x
  disjoint s x
  disjoint s z
  disjoint X s
  disjoint x z
  disjoint X x
  disjoint X z
  disjoint W x
  assert |- ( X e. B -> [_ X / x ]_ O = C )

  proof
    cX
    cB
    wcel
    #
    vx
    cX
    vs
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @1
    vx
    cv
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    @3
    wceq
    #
    wa
    #
    vz
    cv
    #
    cN
    @4
    c.or
    co
    #
    wceq
    #
    wi
    #
    vs
    cA
    wral
    #
    vz
    cB
    crio
    #
    csb
    @2
    @1
    cX
    cW
    c.an
    co
    #
    c.or
    co
    #
    cX
    wceq
    #
    wa
    #
    @8
    cN
    @14
    c.or
    co
    #
    wceq
    #
    wi
    #
    vs
    cA
    wral
    #
    vz
    cB
    crio
    #
    vx
    cX
    cO
    csb
    cC
    vx
    cX
    @13
    @22
    cB
    @0
    vx
    @22
    nfcvd
    @3
    cX
    wceq
    #
    @12
    @21
    vz
    cB
    @23
    @11
    @20
    vs
    cA
    @23
    @7
    @17
    @10
    @19
    @23
    @6
    @16
    @2
    @23
    @5
    @15
    @3
    cX
    @23
    @4
    @14
    @1
    c.or
    @3
    cX
    cW
    c.an
    oveq1
    #
    oveq2d
    @23
    id
    eqeq12d
    anbi2d
    @23
    @9
    @18
    @8
    @23
    @4
    @14
    cN
    c.or
    @24
    oveq2d
    eqeq2d
    imbi12d
    ralbidv
    riotabidv
    csbiegf
    vx
    cX
    cO
    @13
    cdleme31so.o
    csbeq2i
    cdleme31so.c
    3eqtr4g
end
