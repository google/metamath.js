include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cmgp.mm"
include "cress.mm"
include "c0g.mm"
include "wceq.mm"
include "crio.mm"
include "eqid.mm"
include "unitgrpbas.mm"
include "cvv.mm"
include "cplusg.mm"
include "cui.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mgpplusg.mm"
include "ressplusg.mm"
include "ax-mp.mm"
include "invrfval.mm"
include "grpinvval.mm"
include "adantl.mm"
include "unitgrpid.mm"
include "adantr.mm"
include "eqeq2d.mm"
include "riotabidva.mm"
include "eqtr4d.mm"

theorem ringinvval
  let vy: setvar y
  let cB: class B
  let cR: class R
  let cU: class U
  let c.1: class .1.
  let c.as: class .*
  let cN: class N
  let cX: class X
  assume ringinvval.b: |- B = ( Base ` R )
  assume ringinvval.p: |- .* = ( .r ` R )
  assume ringinvval.o: |- .1. = ( 1r ` R )
  assume ringinvval.n: |- N = ( invr ` R )
  assume ringinvval.u: |- U = ( Unit ` R )

  disjoint R y
  disjoint U y
  disjoint X y
  assert |- ( ( R e. Ring /\ X e. U ) -> ( N ` X ) = ( iota_ y e. U ( y .* X ) = .1. ) )

  proof
    cR
    crg
    wcel
    #
    cX
    cU
    wcel
    #
    wa
    cX
    cN
    cfv
    #
    vy
    cv
    #
    cX
    c.as
    co
    #
    cR
    cmgp
    cfv
    #
    cU
    cress
    co
    #
    c0g
    cfv
    #
    wceq
    #
    vy
    cU
    crio
    #
    @4
    c.1
    wceq
    #
    vy
    cU
    crio
    #
    @1
    @2
    @9
    wceq
    @0
    vy
    cU
    c.as
    @6
    cN
    cX
    @7
    cR
    cU
    @6
    ringinvval.u
    @6
    eqid
    #
    unitgrpbas
    cU
    cvv
    wcel
    c.as
    @6
    cplusg
    cfv
    wceq
    cU
    cR
    cui
    cfv
    cvv
    ringinvval.u
    cR
    cui
    fvex
    eqeltri
    cU
    c.as
    @5
    @6
    cvv
    @12
    cR
    c.as
    @5
    @5
    eqid
    ringinvval.p
    mgpplusg
    ressplusg
    ax-mp
    @7
    eqid
    cR
    cU
    @6
    cN
    ringinvval.u
    @12
    ringinvval.n
    invrfval
    grpinvval
    adantl
    @0
    @11
    @9
    wceq
    @1
    @0
    @10
    @8
    vy
    cU
    @0
    @3
    cU
    wcel
    #
    wa
    c.1
    @7
    @4
    @0
    c.1
    @7
    wceq
    @13
    cR
    cU
    c.1
    @6
    ringinvval.u
    @12
    ringinvval.o
    unitgrpid
    adantr
    eqeq2d
    riotabidva
    adantr
    eqtr4d
end
