include "cmpt.mm"
include "cfn.mm"
include "c0g.mm"
include "cfv.mm"
include "eqid.mm"
include "wcel.mm"
include "wral.mm"
include "wf.mm"
include "fmpt.mm"
include "sylib.mm"
include "cvv.mm"
include "wfn.mm"
include "fnmpt.mm"
include "syl.mm"
include "fvexd.mm"
include "fndmfifsupp.mm"
include "gsumcl.mm"

theorem gsummptcl
  let wph: wff ph
  let cB: class B
  let vi: setvar i
  let cG: class G
  let cN: class N
  let cX: class X
  assume gsummptcl.b: |- B = ( Base ` G )
  assume gsummptcl.g: |- ( ph -> G e. CMnd )
  assume gsummptcl.n: |- ( ph -> N e. Fin )
  assume gsummptcl.e: |- ( ph -> A. i e. N X e. B )

  disjoint B i
  disjoint N i
  assert |- ( ph -> ( G gsum ( i e. N |-> X ) ) e. B )

  proof
    wph
    cN
    cB
    vi
    cN
    cX
    cmpt
    #
    cG
    cfn
    cG
    c0g
    cfv
    #
    gsummptcl.b
    @1
    eqid
    gsummptcl.g
    gsummptcl.n
    wph
    cX
    cB
    wcel
    vi
    cN
    wral
    #
    cN
    cB
    @0
    wf
    gsummptcl.e
    vi
    cN
    cB
    cX
    @0
    @0
    eqid
    #
    fmpt
    sylib
    wph
    cN
    @0
    cvv
    @1
    wph
    @2
    @0
    cN
    wfn
    gsummptcl.e
    vi
    cN
    cX
    @0
    cB
    @3
    fnmpt
    syl
    gsummptcl.n
    wph
    cG
    c0g
    fvexd
    fndmfifsupp
    gsumcl
end
