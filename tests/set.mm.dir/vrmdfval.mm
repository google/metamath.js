include "wcel.mm"
include "cvrmd.mm"
include "cfv.mm"
include "cv.mm"
include "cs1.mm"
include "cmpt.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "cword.mm"
include "wf.mm"
include "s1cl.mm"
include "adantl.mm"
include "eqid.mm"
include "fmptd.mm"
include "wrdexg.mm"
include "fex2.mm"
include "syl3anc.mm"
include "mpteq1.mm"
include "df-vrmd.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "syl5eq.mm"

theorem vrmdfval
  let cU: class U
  let vj: setvar j
  let cI: class I
  let cV: class V
  let cA: class A
  let vi: setvar i
  assume vrmdfval.u: |- U = ( varFMnd ` I )

  disjoint I j
  disjoint V j
  disjoint A j
  disjoint i j
  disjoint I i
  assert |- ( I e. V -> U = ( j e. I |-> <" j "> ) )

  proof
    cI
    cV
    wcel
    #
    cU
    cI
    cvrmd
    cfv
    #
    vj
    cI
    vj
    cv
    #
    cs1
    #
    cmpt
    #
    vrmdfval.u
    @0
    cI
    cvv
    wcel
    #
    @4
    cvv
    wcel
    #
    @1
    @4
    wceq
    cI
    cV
    elex
    #
    @0
    cI
    cI
    cword
    #
    @4
    wf
    @5
    @8
    cvv
    wcel
    @6
    @0
    vj
    cI
    @3
    @8
    @4
    @2
    cI
    wcel
    @3
    @8
    wcel
    @0
    @2
    cI
    s1cl
    adantl
    @4
    eqid
    fmptd
    @7
    cI
    cV
    wrdexg
    cI
    @8
    @4
    cvv
    cvv
    fex2
    syl3anc
    vi
    cI
    vj
    vi
    cv
    #
    @3
    cmpt
    @4
    cvv
    cvv
    cvrmd
    vj
    @9
    cI
    @3
    mpteq1
    vi
    vj
    df-vrmd
    fvmptg
    syl2anc
    syl5eq
end
