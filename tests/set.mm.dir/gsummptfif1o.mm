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
include "fvexd.mm"
include "fdmfifsupp.mm"
include "gsumf1o.mm"

theorem gsummptfif1o
  let wph: wff ph
  let cB: class B
  let cC: class C
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cH: class H
  let cN: class N
  let cX: class X
  assume gsummptcl.b: |- B = ( Base ` G )
  assume gsummptcl.g: |- ( ph -> G e. CMnd )
  assume gsummptcl.n: |- ( ph -> N e. Fin )
  assume gsummptcl.e: |- ( ph -> A. i e. N X e. B )
  assume gsummptfif1o.f: |- F = ( i e. N |-> X )
  assume gsummptfif1o.h: |- ( ph -> H : C -1-1-onto-> N )

  disjoint B i
  disjoint N i
  assert |- ( ph -> ( G gsum F ) = ( G gsum ( F o. H ) ) )

  proof
    wph
    cN
    cB
    cC
    cF
    cG
    cH
    cfn
    cG
    c0g
    cfv
    #
    gsummptcl.b
    @0
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
    cN
    cB
    cF
    wf
    gsummptcl.e
    vi
    cN
    cB
    cX
    cF
    gsummptfif1o.f
    fmpt
    sylib
    #
    wph
    cN
    cB
    cF
    cvv
    @0
    @1
    gsummptcl.n
    wph
    cG
    c0g
    fvexd
    fdmfifsupp
    gsummptfif1o.h
    gsumf1o
end
