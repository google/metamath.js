include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "wrex.mm"
include "notbid.mm"
include "ceqsrexv2.mm"
include "rexanali.mm"
include "annim.mm"
include "3bitr3i.mm"
include "con4bii.mm"

theorem ceqsralv2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume ceqsralv2.1: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  disjoint B x
  disjoint ps x
  assert |- ( A. x e. B ( x = A -> ph ) <-> ( A e. B -> ps ) )

  proof
    vx
    cv
    cA
    wceq
    #
    wph
    wi
    vx
    cB
    wral
    #
    cA
    cB
    wcel
    #
    wps
    wi
    #
    @0
    wph
    wn
    #
    wa
    vx
    cB
    wrex
    @2
    wps
    wn
    #
    wa
    @1
    wn
    @3
    wn
    @4
    @5
    vx
    cA
    cB
    @0
    wph
    wps
    ceqsralv2.1
    notbid
    ceqsrexv2
    @0
    wph
    vx
    cB
    rexanali
    @2
    wps
    annim
    3bitr3i
    con4bii
end
