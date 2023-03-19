include "wcel.mm"
include "cvv.mm"
include "weu.mm"
include "cio.mm"
include "wceq.mm"
include "wb.mm"
include "elex.mm"
include "wa.mm"
include "simpl.mm"
include "simpr.mm"
include "cv.mm"
include "adantl.mm"
include "nfv.mm"
include "nfeu1.mm"
include "nfan.mm"
include "nfvd.mm"
include "nfcvd.mm"
include "iota2df.mm"
include "sylan.mm"

theorem iota2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume iota2.1: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  disjoint ps x
  assert |- ( ( A e. B /\ E! x ph ) -> ( ps <-> ( iota x ph ) = A ) )

  proof
    cA
    cB
    wcel
    cA
    cvv
    wcel
    #
    wph
    vx
    weu
    #
    wps
    wph
    vx
    cio
    cA
    wceq
    wb
    cA
    cB
    elex
    @0
    @1
    wa
    #
    wph
    wps
    vx
    cA
    cvv
    @0
    @1
    simpl
    @0
    @1
    simpr
    vx
    cv
    cA
    wceq
    wph
    wps
    wb
    @2
    iota2.1
    adantl
    @0
    @1
    vx
    @0
    vx
    nfv
    wph
    vx
    nfeu1
    nfan
    @2
    wps
    vx
    nfvd
    @2
    vx
    cA
    nfcvd
    iota2df
    sylan
end
