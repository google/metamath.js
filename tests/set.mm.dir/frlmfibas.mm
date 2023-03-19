include "wcel.mm"
include "cfn.mm"
include "wa.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "c0g.mm"
include "cfv.mm"
include "cfsupp.mm"
include "wbr.mm"
include "crab.mm"
include "cbs.mm"
include "wral.mm"
include "wceq.mm"
include "cvv.mm"
include "wf.mm"
include "elmapi.mm"
include "adantl.mm"
include "simpl.mm"
include "fvexd.mm"
include "fdmfifsupp.mm"
include "ralrimiva.mm"
include "rabid2.mm"
include "sylibr.mm"
include "eqid.mm"
include "frlmbas.mm"
include "eqtrd.mm"

theorem frlmfibas
  let cR: class R
  let cF: class F
  let cI: class I
  let cN: class N
  let cV: class V
  let va: setvar a
  assume frlmfibas.f: |- F = ( R freeLMod I )
  assume frlmfibas.n: |- N = ( Base ` R )


  assert |- ( ( R e. V /\ I e. Fin ) -> ( N ^m I ) = ( Base ` F ) )

  proof
    cR
    cV
    wcel
    #
    cI
    cfn
    wcel
    #
    wa
    #
    cN
    cI
    cmap
    co
    #
    va
    cv
    #
    cR
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    va
    @3
    crab
    #
    cF
    cbs
    cfv
    @2
    @6
    va
    @3
    wral
    #
    @3
    @7
    wceq
    @1
    @8
    @0
    @1
    @6
    va
    @3
    @1
    @4
    @3
    wcel
    #
    wa
    #
    cI
    cN
    @4
    cvv
    @5
    @9
    cI
    cN
    @4
    wf
    @1
    @4
    cN
    cI
    elmapi
    adantl
    @1
    @9
    simpl
    @10
    cR
    c0g
    fvexd
    fdmfifsupp
    ralrimiva
    adantl
    @6
    va
    @3
    rabid2
    sylibr
    @7
    cR
    va
    cF
    cI
    cN
    cV
    cfn
    @5
    frlmfibas.f
    frlmfibas.n
    @5
    eqid
    @7
    eqid
    frlmbas
    eqtrd
end
