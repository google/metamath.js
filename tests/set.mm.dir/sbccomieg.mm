include "wsbc.mm"
include "cvv.mm"
include "wcel.mm"
include "sbcex.mm"
include "wex.mm"
include "spesbc.mm"
include "exlimiv.mm"
include "syl.mm"
include "nfcv.mm"
include "nfsbc1v.mm"
include "nfsbc.mm"
include "cv.mm"
include "wceq.mm"
include "sbceq1a.mm"
include "sbceqbid.mm"
include "sbciegf.mm"
include "pm5.21nii.mm"

theorem sbccomieg
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let va: setvar a
  let vb: setvar b
  assume sbccomieg.1: |- ( a = A -> B = C )

  disjoint A a
  disjoint A b
  disjoint a b
  disjoint C a
  assert |- ( [. A / a ]. [. B / b ]. ph <-> [. C / b ]. [. A / a ]. ph )

  proof
    wph
    vb
    cB
    wsbc
    #
    va
    cA
    wsbc
    cA
    cvv
    wcel
    #
    wph
    va
    cA
    wsbc
    #
    vb
    cC
    wsbc
    #
    @0
    va
    cA
    sbcex
    @3
    @2
    vb
    wex
    @1
    @2
    vb
    cC
    spesbc
    @2
    @1
    vb
    wph
    va
    cA
    sbcex
    exlimiv
    syl
    @0
    @3
    va
    cA
    cvv
    @2
    va
    vb
    cC
    va
    cC
    nfcv
    wph
    va
    cA
    nfsbc1v
    nfsbc
    va
    cv
    cA
    wceq
    wph
    @2
    vb
    cB
    cC
    sbccomieg.1
    wph
    va
    cA
    sbceq1a
    sbceqbid
    sbciegf
    pm5.21nii
end
