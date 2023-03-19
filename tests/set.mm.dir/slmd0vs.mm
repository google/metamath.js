include "cslmd.mm"
include "wcel.mm"
include "wa.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cur.mm"
include "cplusg.mm"
include "w3a.mm"
include "cbs.mm"
include "simpl.mm"
include "eqid.mm"
include "slmd0cl.mm"
include "adantr.mm"
include "simpr.mm"
include "slmdlema.mm"
include "syl122anc.mm"
include "simprd.mm"
include "simp3d.mm"

theorem slmd0vs
  let c.x: class .x.
  let cF: class F
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume slmd0vs.v: |- V = ( Base ` W )
  assume slmd0vs.f: |- F = ( Scalar ` W )
  assume slmd0vs.s: |- .x. = ( .s ` W )
  assume slmd0vs.o: |- O = ( 0g ` F )
  assume slmd0vs.z: |- .0. = ( 0g ` W )


  assert |- ( ( W e. SLMod /\ X e. V ) -> ( O .x. X ) = .0. )

  proof
    cW
    cslmd
    wcel
    #
    cX
    cV
    wcel
    #
    wa
    #
    cO
    cO
    cF
    cmulr
    cfv
    #
    co
    cX
    c.x
    co
    cO
    cO
    cX
    c.x
    co
    #
    c.x
    co
    wceq
    #
    cF
    cur
    cfv
    #
    cX
    c.x
    co
    cX
    wceq
    #
    @4
    c.0
    wceq
    #
    @2
    @4
    cV
    wcel
    cO
    cX
    cX
    cW
    cplusg
    cfv
    #
    co
    c.x
    co
    @4
    @4
    @9
    co
    #
    wceq
    cO
    cO
    cF
    cplusg
    cfv
    #
    co
    cX
    c.x
    co
    @10
    wceq
    w3a
    #
    @5
    @7
    @8
    w3a
    #
    @2
    @0
    cO
    cF
    cbs
    cfv
    #
    wcel
    #
    @15
    @1
    @1
    @12
    @13
    wa
    @0
    @1
    simpl
    @0
    @15
    @1
    cF
    @14
    cW
    cO
    slmd0vs.f
    @14
    eqid
    #
    slmd0vs.o
    slmd0cl
    adantr
    #
    @17
    @0
    @1
    simpr
    #
    @18
    @9
    @11
    cO
    cO
    c.x
    @3
    @6
    cF
    @14
    cO
    cV
    cW
    cX
    cX
    c.0
    slmd0vs.v
    @9
    eqid
    slmd0vs.s
    slmd0vs.z
    slmd0vs.f
    @16
    @11
    eqid
    @3
    eqid
    @6
    eqid
    slmd0vs.o
    slmdlema
    syl122anc
    simprd
    simp3d
end
