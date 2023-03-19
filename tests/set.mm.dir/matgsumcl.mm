include "ccrg.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "eqid.mm"
include "mgpbas.mm"
include "ccmn.mm"
include "crngmgp.mm"
include "adantr.mm"
include "cfn.mm"
include "cvv.mm"
include "matrcl.mm"
include "adantl.mm"
include "simpld.mm"
include "cxp.mm"
include "wf.mm"
include "cmap.mm"
include "simpr.mm"
include "matbas2i.mm"
include "elmapi.mm"
include "3syl.mm"
include "fovrnd.mm"
include "ralrimiva.mm"
include "gsummptcl.mm"

theorem matgsumcl
  let cA: class A
  let cB: class B
  let cR: class R
  let cU: class U
  let cM: class M
  let cN: class N
  let vr: setvar r
  assume madetsumid.a: |- A = ( N Mat R )
  assume madetsumid.b: |- B = ( Base ` A )
  assume madetsumid.u: |- U = ( mulGrp ` R )

  disjoint B r
  disjoint M r
  disjoint N r
  disjoint R r
  assert |- ( ( R e. CRing /\ M e. B ) -> ( U gsum ( r e. N |-> ( r M r ) ) ) e. ( Base ` R ) )

  proof
    cR
    ccrg
    wcel
    #
    cM
    cB
    wcel
    #
    wa
    #
    cR
    cbs
    cfv
    #
    vr
    cU
    cN
    vr
    cv
    #
    @4
    cM
    co
    #
    @3
    cR
    cU
    madetsumid.u
    @3
    eqid
    #
    mgpbas
    @0
    cU
    ccmn
    wcel
    @1
    cR
    cU
    madetsumid.u
    crngmgp
    adantr
    @2
    cN
    cfn
    wcel
    #
    cR
    cvv
    wcel
    #
    @1
    @7
    @8
    wa
    @0
    cA
    cB
    cR
    cN
    cM
    madetsumid.a
    madetsumid.b
    matrcl
    adantl
    simpld
    @2
    @5
    @3
    wcel
    vr
    cN
    @2
    @4
    cN
    wcel
    #
    wa
    @4
    @4
    @3
    cN
    cN
    cM
    @2
    cN
    cN
    cxp
    #
    @3
    cM
    wf
    #
    @9
    @2
    @1
    cM
    @3
    @10
    cmap
    co
    wcel
    @11
    @0
    @1
    simpr
    cA
    cB
    cR
    @3
    cM
    cN
    madetsumid.a
    @6
    madetsumid.b
    matbas2i
    cM
    @3
    @10
    elmapi
    3syl
    adantr
    @2
    @9
    simpr
    #
    @12
    fovrnd
    ralrimiva
    gsummptcl
end
