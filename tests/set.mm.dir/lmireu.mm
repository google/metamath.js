include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "lmicl.mm"
include "lmilmi.mm"
include "wa.mm"
include "cstrkg.mm"
include "ad2antrr.mm"
include "c2.mm"
include "cstrkgld.mm"
include "wbr.mm"
include "crn.mm"
include "simplr.mm"
include "simpr.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "ex.mm"
include "ralrimiva.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "eqreu.mm"
include "syl3anc.mm"

theorem lmireu
  let wph: wff ph
  let cA: class A
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let vb: setvar b
  let vm: setvar m
  let va: setvar a
  let vg: setvar g
  let vd: setvar d
  assume ismid.p: |- P = ( Base ` G )
  assume ismid.d: |- .- = ( dist ` G )
  assume ismid.i: |- I = ( Itv ` G )
  assume ismid.g: |- ( ph -> G e. TarskiG )
  assume ismid.1: |- ( ph -> G TarskiGDim>= 2 )
  assume lmif.m: |- M = ( ( lInvG ` G ) ` D )
  assume lmif.l: |- L = ( LineG ` G )
  assume lmif.d: |- ( ph -> D e. ran L )
  assume lmicl.1: |- ( ph -> A e. P )

  disjoint A b
  disjoint M b
  disjoint G b
  disjoint P b
  disjoint b ph
  disjoint D b
  disjoint L b
  disjoint .- m
  disjoint G a
  disjoint G g
  disjoint G m
  disjoint a b
  disjoint a g
  disjoint a m
  disjoint b g
  disjoint b m
  disjoint g m
  disjoint I m
  disjoint L m
  disjoint P a
  disjoint P g
  disjoint P m
  disjoint a ph
  disjoint g ph
  disjoint m ph
  disjoint D a
  disjoint D d
  disjoint a d
  disjoint b d
  disjoint G d
  disjoint d g
  disjoint L a
  disjoint L d
  disjoint L g
  disjoint P d
  disjoint d ph
  assert |- ( ph -> E! b e. P ( M ` b ) = A )

  proof
    wph
    cA
    cM
    cfv
    #
    cP
    wcel
    @0
    cM
    cfv
    #
    cA
    wceq
    #
    vb
    cv
    #
    cM
    cfv
    #
    cA
    wceq
    #
    @3
    @0
    wceq
    #
    wi
    #
    vb
    cP
    wral
    @5
    vb
    cP
    wreu
    wph
    cA
    cD
    cP
    cG
    cI
    cL
    cM
    c.mi
    ismid.p
    ismid.d
    ismid.i
    ismid.g
    ismid.1
    lmif.m
    lmif.l
    lmif.d
    lmicl.1
    lmicl
    wph
    cA
    cD
    cP
    cG
    cI
    cL
    cM
    c.mi
    ismid.p
    ismid.d
    ismid.i
    ismid.g
    ismid.1
    lmif.m
    lmif.l
    lmif.d
    lmicl.1
    lmilmi
    wph
    @7
    vb
    cP
    wph
    @3
    cP
    wcel
    #
    wa
    #
    @5
    @6
    @9
    @5
    wa
    #
    @4
    cM
    cfv
    @3
    @0
    @10
    @3
    cD
    cP
    cG
    cI
    cL
    cM
    c.mi
    ismid.p
    ismid.d
    ismid.i
    wph
    cG
    cstrkg
    wcel
    @8
    @5
    ismid.g
    ad2antrr
    wph
    cG
    c2
    cstrkgld
    wbr
    @8
    @5
    ismid.1
    ad2antrr
    lmif.m
    lmif.l
    wph
    cD
    cL
    crn
    wcel
    @8
    @5
    lmif.d
    ad2antrr
    wph
    @8
    @5
    simplr
    lmilmi
    @10
    @4
    cA
    cM
    @9
    @5
    simpr
    fveq2d
    eqtr3d
    ex
    ralrimiva
    @5
    @2
    vb
    cP
    @0
    @6
    @4
    @1
    cA
    @3
    @0
    cM
    fveq2
    eqeq1d
    eqreu
    syl3anc
end
