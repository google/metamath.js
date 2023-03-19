include "wcel.mm"
include "cword.mm"
include "wf.mm"
include "cv.mm"
include "cs1.mm"
include "cmpt.mm"
include "s1cl.mm"
include "adantl.mm"
include "eqid.mm"
include "fmptd.mm"
include "vrmdfval.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem vrmdf
  let cU: class U
  let cI: class I
  let cV: class V
  let cA: class A
  let vj: setvar j
  let vi: setvar i
  assume vrmdfval.u: |- U = ( varFMnd ` I )


  assert |- ( I e. V -> U : I --> Word I )

  proof
    cI
    cV
    wcel
    #
    cI
    cI
    cword
    #
    cU
    wf
    cI
    @1
    vj
    cI
    vj
    cv
    #
    cs1
    #
    cmpt
    #
    wf
    @0
    vj
    cI
    @3
    @1
    @4
    @2
    cI
    wcel
    @3
    @1
    wcel
    @0
    @2
    cI
    s1cl
    adantl
    @4
    eqid
    fmptd
    @0
    cI
    @1
    cU
    @4
    cU
    vj
    cI
    cV
    vrmdfval.u
    vrmdfval
    feq1d
    mpbird
end
