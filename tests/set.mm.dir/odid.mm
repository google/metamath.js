include "wcel.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cv.mm"
include "co.mm"
include "cn.mm"
include "crab.mm"
include "c0.mm"
include "wa.mm"
include "oveq1.mm"
include "mulg0.mm"
include "sylan9eqr.mm"
include "adantrr.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "simprbi.mm"
include "adantl.mm"
include "eqid.mm"
include "odlem1.mm"
include "mpjaodan.mm"

theorem odid
  let cA: class A
  let c.x: class .x.
  let cG: class G
  let cO: class O
  let cX: class X
  let c.0: class .0.
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vx: setvar x
  let cN: class N
  assume odcl.1: |- X = ( Base ` G )
  assume odcl.2: |- O = ( od ` G )
  assume odid.3: |- .x. = ( .g ` G )
  assume odid.4: |- .0. = ( 0g ` G )


  assert |- ( A e. X -> ( ( O ` A ) .x. A ) = .0. )

  proof
    cA
    cX
    wcel
    #
    cA
    cO
    cfv
    #
    cc0
    wceq
    #
    vy
    cv
    #
    cA
    c.x
    co
    #
    c.0
    wceq
    #
    vy
    cn
    crab
    #
    c0
    wceq
    #
    wa
    @1
    cA
    c.x
    co
    #
    c.0
    wceq
    #
    @1
    @6
    wcel
    #
    @0
    @2
    @9
    @7
    @2
    @0
    @8
    cc0
    cA
    c.x
    co
    c.0
    @1
    cc0
    cA
    c.x
    oveq1
    cX
    c.x
    cG
    cA
    c.0
    odcl.1
    odid.4
    odid.3
    mulg0
    sylan9eqr
    adantrr
    @10
    @9
    @0
    @10
    @1
    cn
    wcel
    @9
    @5
    @9
    vy
    @1
    cn
    @3
    @1
    wceq
    @4
    @8
    c.0
    @3
    @1
    cA
    c.x
    oveq1
    eqeq1d
    elrab
    simprbi
    adantl
    vy
    cA
    c.x
    cG
    @6
    cO
    cX
    c.0
    odcl.1
    odid.3
    odid.4
    odcl.2
    @6
    eqid
    odlem1
    mpjaodan
end
