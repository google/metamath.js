include "wnf.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wi.mm"
include "wal.mm"
include "wcel.mm"
include "wral.mm"
include "nfv.mm"
include "ax-gen.mm"
include "ceqsralt.mm"
include "mp3an12.mm"

theorem ceqsralv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume ceqsralv.2: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  disjoint B x
  disjoint ps x
  assert |- ( A e. B -> ( A. x e. B ( x = A -> ph ) <-> ps ) )

  proof
    wps
    vx
    wnf
    vx
    cv
    cA
    wceq
    #
    wph
    wps
    wb
    wi
    #
    vx
    wal
    cA
    cB
    wcel
    @0
    wph
    wi
    vx
    cB
    wral
    wps
    wb
    wps
    vx
    nfv
    @1
    vx
    ceqsralv.2
    ax-gen
    wph
    wps
    vx
    cA
    cB
    ceqsralt
    mp3an12
end
