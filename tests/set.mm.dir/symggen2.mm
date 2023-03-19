include "cfn.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "crab.mm"
include "symggen.mm"
include "wral.mm"
include "wceq.mm"
include "wss.mm"
include "difss.mm"
include "dmss.mm"
include "ax-mp.mm"
include "wf1o.mm"
include "symgbasf1o.mm"
include "f1odm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "ssfi.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "rabid2.mm"
include "sylibr.mm"
include "eqtr4d.mm"

theorem symggen2
  let cB: class B
  let cD: class D
  let cT: class T
  let cG: class G
  let cK: class K
  let vx: setvar x
  let vu: setvar u
  let vy: setvar y
  let vz: setvar z
  let cV: class V
  assume symgtrf.t: |- T = ran ( pmTrsp ` D )
  assume symgtrf.g: |- G = ( SymGrp ` D )
  assume symgtrf.b: |- B = ( Base ` G )
  assume symggen.k: |- K = ( mrCls ` ( SubMnd ` G ) )


  assert |- ( D e. Fin -> ( K ` T ) = B )

  proof
    cD
    cfn
    wcel
    #
    cT
    cK
    cfv
    vx
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
    vx
    cB
    crab
    #
    cB
    vx
    cB
    cD
    cT
    cG
    cK
    cfn
    symgtrf.t
    symgtrf.g
    symgtrf.b
    symggen.k
    symggen
    @0
    @4
    vx
    cB
    wral
    cB
    @5
    wceq
    @0
    @4
    vx
    cB
    @1
    cB
    wcel
    #
    @0
    @3
    cD
    wss
    @4
    @6
    @1
    cdm
    #
    @3
    cD
    @2
    @1
    wss
    @3
    @7
    wss
    @1
    cid
    difss
    @2
    @1
    dmss
    ax-mp
    @6
    cD
    cD
    @1
    wf1o
    @7
    cD
    wceq
    cD
    cB
    @1
    cG
    symgtrf.g
    symgtrf.b
    symgbasf1o
    cD
    cD
    @1
    f1odm
    syl
    syl5sseq
    cD
    @3
    ssfi
    sylan2
    ralrimiva
    @4
    vx
    cB
    rabid2
    sylibr
    eqtr4d
end
