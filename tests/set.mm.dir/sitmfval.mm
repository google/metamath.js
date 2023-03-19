include "csitg.mm"
include "co.mm"
include "cdm.mm"
include "cv.mm"
include "cof.mm"
include "cxrs.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "cress.mm"
include "cfv.mm"
include "csitm.mm"
include "cvv.mm"
include "sitmval.mm"
include "wceq.mm"
include "wa.mm"
include "simprl.mm"
include "simprr.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "fvexd.mm"
include "ovmpt2d.mm"

theorem sitmfval
  let wph: wff ph
  let cD: class D
  let cF: class F
  let cG: class G
  let cM: class M
  let cV: class V
  let cW: class W
  let vm: setvar m
  let vw: setvar w
  let vf: setvar f
  let vg: setvar g
  assume sitmval.d: |- D = ( dist ` W )
  assume sitmval.1: |- ( ph -> W e. V )
  assume sitmval.2: |- ( ph -> M e. U. ran measures )
  assume sitmfval.1: |- ( ph -> F e. dom ( W sitg M ) )
  assume sitmfval.2: |- ( ph -> G e. dom ( W sitg M ) )


  assert |- ( ph -> ( F ( W sitm M ) G ) = ( ( ( RR*s |`s ( 0 [,] +oo ) ) sitg M ) ` ( F oF D G ) ) )

  proof
    wph
    vf
    vg
    cF
    cG
    cW
    cM
    csitg
    co
    cdm
    #
    @0
    vf
    cv
    #
    vg
    cv
    #
    cD
    cof
    #
    co
    #
    cxrs
    cc0
    cpnf
    cicc
    co
    cress
    co
    cM
    csitg
    co
    #
    cfv
    cF
    cG
    @3
    co
    #
    @5
    cfv
    cW
    cM
    csitm
    co
    cvv
    wph
    cD
    vf
    vg
    cM
    cV
    cW
    sitmval.d
    sitmval.1
    sitmval.2
    sitmval
    wph
    @1
    cF
    wceq
    #
    @2
    cG
    wceq
    #
    wa
    wa
    #
    @4
    @6
    @5
    @9
    @1
    cF
    @2
    cG
    @3
    wph
    @7
    @8
    simprl
    wph
    @7
    @8
    simprr
    oveq12d
    fveq2d
    sitmfval.1
    sitmfval.2
    wph
    @6
    @5
    fvexd
    ovmpt2d
end
