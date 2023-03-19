include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "crab.mm"
include "wfn.mm"
include "ccom.mm"
include "cfv.mm"
include "wceq.mm"
include "csymg.mm"
include "eqid.mm"
include "psgnfn.mm"
include "simpr.mm"
include "sygbasnfpfi.mm"
include "difeq1.mm"
include "dmeqd.mm"
include "eleq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "fvco2.mm"
include "sylancr.mm"

theorem zrhcofipsgn
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cN: class N
  let cY: class Y
  let vp: setvar p
  assume zrhcofipsgn.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume zrhcofipsgn.y: |- Y = ( ZRHom ` R )
  assume zrhcofipsgn.s: |- S = ( pmSgn ` N )


  assert |- ( ( N e. Fin /\ Q e. P ) -> ( ( Y o. S ) ` Q ) = ( Y ` ( S ` Q ) ) )

  proof
    cN
    cfn
    wcel
    #
    cQ
    cP
    wcel
    #
    wa
    #
    cS
    vp
    cv
    #
    cid
    cdif
    #
    cdm
    #
    cfn
    wcel
    #
    vp
    cP
    crab
    #
    wfn
    cQ
    @7
    wcel
    #
    cQ
    cY
    cS
    ccom
    cfv
    cQ
    cS
    cfv
    cY
    cfv
    wceq
    cP
    cN
    @7
    cN
    csymg
    cfv
    #
    cS
    vp
    @9
    eqid
    #
    zrhcofipsgn.p
    @7
    eqid
    zrhcofipsgn.s
    psgnfn
    @2
    @1
    cQ
    cid
    cdif
    #
    cdm
    #
    cfn
    wcel
    #
    @8
    @0
    @1
    simpr
    cP
    cN
    cQ
    @9
    @10
    zrhcofipsgn.p
    sygbasnfpfi
    @6
    @13
    vp
    cQ
    cP
    @3
    cQ
    wceq
    #
    @5
    @12
    cfn
    @14
    @4
    @11
    @3
    cQ
    cid
    difeq1
    dmeqd
    eleq1d
    elrab
    sylanbrc
    @7
    cY
    cS
    cQ
    fvco2
    sylancr
end
