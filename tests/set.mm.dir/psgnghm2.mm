include "cfn.mm"
include "wcel.mm"
include "cdm.mm"
include "cress.mm"
include "co.mm"
include "cghm.mm"
include "eqid.mm"
include "psgnghm.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "wss.mm"
include "cv.mm"
include "cid.mm"
include "cdif.mm"
include "crab.mm"
include "wral.mm"
include "sygbasnfpfi.mm"
include "ralrimiva.mm"
include "rabid2.mm"
include "sylibr.mm"
include "wfn.mm"
include "psgnfn.mm"
include "fndm.mm"
include "ax-mp.mm"
include "syl6eqr.mm"
include "eqimss.mm"
include "cvv.mm"
include "csymg.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cpsgn.mm"
include "dmex.mm"
include "ressid2.mm"
include "mp3an23.mm"
include "3syl.mm"
include "oveq1d.mm"
include "eleqtrd.mm"

theorem psgnghm2
  let cD: class D
  let cS: class S
  let cU: class U
  let cN: class N
  let vx: setvar x
  assume psgnghm2.s: |- S = ( SymGrp ` D )
  assume psgnghm2.n: |- N = ( pmSgn ` D )
  assume psgnghm2.u: |- U = ( ( mulGrp ` CCfld ) |`s { 1 , -u 1 } )


  assert |- ( D e. Fin -> N e. ( S GrpHom U ) )

  proof
    cD
    cfn
    wcel
    #
    cN
    cS
    cN
    cdm
    #
    cress
    co
    #
    cU
    cghm
    co
    cS
    cU
    cghm
    co
    cD
    cS
    cU
    @2
    cN
    cfn
    psgnghm2.s
    psgnghm2.n
    @2
    eqid
    #
    psgnghm2.u
    psgnghm
    @0
    @2
    cS
    cU
    cghm
    @0
    cS
    cbs
    cfv
    #
    @1
    wceq
    @4
    @1
    wss
    #
    @2
    cS
    wceq
    #
    @0
    @4
    vx
    cv
    #
    cid
    cdif
    cdm
    cfn
    wcel
    #
    vx
    @4
    crab
    #
    @1
    @0
    @8
    vx
    @4
    wral
    @4
    @9
    wceq
    @0
    @8
    vx
    @4
    @4
    cD
    @7
    cS
    psgnghm2.s
    @4
    eqid
    #
    sygbasnfpfi
    ralrimiva
    @8
    vx
    @4
    rabid2
    sylibr
    cN
    @9
    wfn
    @1
    @9
    wceq
    @4
    cD
    @9
    cS
    cN
    vx
    psgnghm2.s
    @10
    @9
    eqid
    psgnghm2.n
    psgnfn
    @9
    cN
    fndm
    ax-mp
    syl6eqr
    @4
    @1
    eqimss
    @5
    cS
    cvv
    wcel
    @1
    cvv
    wcel
    @6
    cS
    cD
    csymg
    cfv
    cvv
    psgnghm2.s
    cD
    csymg
    fvex
    eqeltri
    cN
    cN
    cD
    cpsgn
    cfv
    cvv
    psgnghm2.n
    cD
    cpsgn
    fvex
    eqeltri
    dmex
    @1
    @4
    @2
    cS
    cvv
    cvv
    @3
    @10
    ressid2
    mp3an23
    3syl
    oveq1d
    eleqtrd
end
