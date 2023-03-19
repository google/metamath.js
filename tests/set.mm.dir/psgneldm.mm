include "cv.mm"
include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "cfn.mm"
include "wcel.mm"
include "wceq.mm"
include "difeq1.mm"
include "dmeqd.mm"
include "eleq1d.mm"
include "crab.mm"
include "wfn.mm"
include "eqid.mm"
include "psgnfn.mm"
include "fndm.mm"
include "ax-mp.mm"
include "elrab2.mm"

theorem psgneldm
  let cB: class B
  let cD: class D
  let cP: class P
  let cG: class G
  let cN: class N
  let vp: setvar p
  assume psgneldm.g: |- G = ( SymGrp ` D )
  assume psgneldm.n: |- N = ( pmSgn ` D )
  assume psgneldm.b: |- B = ( Base ` G )


  assert |- ( P e. dom N <-> ( P e. B /\ dom ( P \ _I ) e. Fin ) )

  proof
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
    cP
    cid
    cdif
    #
    cdm
    #
    cfn
    wcel
    vp
    cP
    cB
    cN
    cdm
    #
    @0
    cP
    wceq
    #
    @2
    @5
    cfn
    @7
    @1
    @4
    @0
    cP
    cid
    difeq1
    dmeqd
    eleq1d
    cN
    @3
    vp
    cB
    crab
    #
    wfn
    @6
    @8
    wceq
    cB
    cD
    @8
    cG
    cN
    vp
    psgneldm.g
    psgneldm.b
    @8
    eqid
    psgneldm.n
    psgnfn
    @8
    cN
    fndm
    ax-mp
    elrab2
end
