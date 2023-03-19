include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cmap.mm"
include "co.mm"
include "c0g.mm"
include "cfv.mm"
include "cfsupp.mm"
include "wbr.mm"
include "clinc.mm"
include "wceq.mm"
include "cvv.mm"
include "simpr.mm"
include "eqid.mm"
include "lmod0cl.mm"
include "adantr.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "mapsnop.mm"
include "syl3anc.mm"
include "wf.mm"
include "elmapi.mm"
include "syl.mm"
include "cfn.mm"
include "snfi.mm"
include "fdmfifsupp.mm"
include "lincval1.mm"
include "3jca.mm"

theorem lcosn0
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


  assert |- ( ( M e. LMod /\ V e. B ) -> ( F e. ( R ^m { V } ) /\ F finSupp ( 0g ` S ) /\ ( F ( linC ` M ) { V } ) = ( 0g ` M ) ) )

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
    #
    cF
    cR
    cV
    csn
    #
    cmap
    co
    wcel
    #
    cF
    cS
    c0g
    cfv
    #
    cfsupp
    wbr
    cF
    @3
    cM
    clinc
    cfv
    co
    cM
    c0g
    cfv
    wceq
    @2
    @1
    @5
    cR
    wcel
    #
    cR
    cvv
    wcel
    #
    @4
    @0
    @1
    simpr
    @0
    @6
    @1
    cS
    cR
    cM
    @5
    lincval1.s
    lincval1.r
    @5
    eqid
    lmod0cl
    adantr
    @7
    @2
    cR
    cS
    cbs
    cfv
    cvv
    lincval1.r
    cS
    cbs
    fvex
    eqeltri
    a1i
    cR
    cF
    cB
    cvv
    cV
    @5
    lincval1.f
    mapsnop
    syl3anc
    #
    @2
    @3
    cR
    cF
    cvv
    @5
    @2
    @4
    @3
    cR
    cF
    wf
    @8
    cF
    cR
    @3
    elmapi
    syl
    @3
    cfn
    wcel
    @2
    cV
    snfi
    a1i
    @5
    cvv
    wcel
    @2
    cS
    c0g
    fvex
    a1i
    fdmfifsupp
    cB
    cR
    cS
    cF
    cM
    cV
    lincval1.b
    lincval1.s
    lincval1.r
    lincval1.f
    lincval1
    3jca
end
