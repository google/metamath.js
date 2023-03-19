include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "clinc.mm"
include "cfv.mm"
include "co.mm"
include "c0g.mm"
include "cvsca.mm"
include "wceq.mm"
include "eqid.mm"
include "lmod0cl.mm"
include "adantr.mm"
include "lincvalsn.mm"
include "mpd3an3.mm"
include "lmod0vs.mm"
include "eqtrd.mm"

theorem lincval1
  let cB: class B
  let cR: class R
  let cS: class S
  let cF: class F
  let cM: class M
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  assume lincval1.b: |- B = ( Base ` M )
  assume lincval1.s: |- S = ( Scalar ` M )
  assume lincval1.r: |- R = ( Base ` S )
  assume lincval1.f: |- F = { <. V , ( 0g ` S ) >. }


  assert |- ( ( M e. LMod /\ V e. B ) -> ( F ( linC ` M ) { V } ) = ( 0g ` M ) )

  proof
    cM
    clmod
    wcel
    #
    cV
    cB
    wcel
    #
    wa
    cF
    cV
    csn
    cM
    clinc
    cfv
    co
    #
    cS
    c0g
    cfv
    #
    cV
    cM
    cvsca
    cfv
    #
    co
    #
    cM
    c0g
    cfv
    #
    @0
    @1
    @3
    cR
    wcel
    #
    @2
    @5
    wceq
    @0
    @7
    @1
    cS
    cR
    cM
    @3
    lincval1.s
    lincval1.r
    @3
    eqid
    #
    lmod0cl
    adantr
    cB
    cR
    cS
    @4
    cF
    cM
    cV
    @3
    lincval1.b
    lincval1.s
    lincval1.r
    @4
    eqid
    #
    lincval1.f
    lincvalsn
    mpd3an3
    @4
    cS
    @3
    cB
    cM
    cV
    @6
    lincval1.b
    lincval1.s
    @9
    @8
    @6
    eqid
    lmod0vs
    eqtrd
end
