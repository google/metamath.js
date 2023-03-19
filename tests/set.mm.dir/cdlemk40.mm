include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cif.mm"
include "csb.mm"
include "cvv.mm"
include "vex.mm"
include "crio.mm"
include "riotaex.mm"
include "eqeltri.mm"
include "ifex.mm"
include "csbex.mm"
include "fvmpts.mm"
include "mpan2.mm"
include "wsbc.mm"
include "csbif.mm"
include "sbcg.mm"
include "csbvarg.mm"
include "ifbieq1d.mm"
include "syl5eq.mm"
include "eqtrd.mm"

theorem cdlemk40
  let wph: wff ph
  let vz: setvar z
  let cT: class T
  let cU: class U
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cN: class N
  let cX: class X
  assume cdlemk40.x: |- X = ( iota_ z e. T ph )
  assume cdlemk40.u: |- U = ( g e. T |-> if ( F = N , g , X ) )

  disjoint F g
  disjoint N g
  disjoint T g
  assert |- ( G e. T -> ( U ` G ) = if ( F = N , G , [_ G / g ]_ X ) )

  proof
    cG
    cT
    wcel
    #
    cG
    cU
    cfv
    #
    vg
    cG
    cF
    cN
    wceq
    #
    vg
    cv
    #
    cX
    cif
    #
    csb
    #
    @2
    cG
    vg
    cG
    cX
    csb
    #
    cif
    #
    @0
    @5
    cvv
    wcel
    @1
    @5
    wceq
    vg
    cG
    @4
    @2
    @3
    cX
    vg
    vex
    cX
    wph
    vz
    cT
    crio
    cvv
    cdlemk40.x
    wph
    vz
    cT
    riotaex
    eqeltri
    ifex
    csbex
    vg
    cG
    @4
    cT
    cU
    cvv
    cdlemk40.u
    fvmpts
    mpan2
    @0
    @5
    @2
    vg
    cG
    wsbc
    #
    vg
    cG
    @3
    csb
    #
    @6
    cif
    @7
    @2
    vg
    cG
    @3
    cX
    csbif
    @0
    @8
    @2
    @9
    cG
    @6
    @2
    vg
    cG
    cT
    sbcg
    vg
    cG
    cT
    csbvarg
    ifbieq1d
    syl5eq
    eqtrd
end
