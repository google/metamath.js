include "wceq.mm"
include "wal.mm"
include "wral.mm"
include "cmpt.mm"
include "alrimi.mm"
include "eqid.mm"
include "rgenw.mm"
include "a1i.mm"
include "mpteq12f.mm"
include "syl2anc.mm"

theorem mpteq1df
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume mpteq1df.1: |- F/ x ph
  assume mpteq1df.2: |- ( ph -> A = B )


  assert |- ( ph -> ( x e. A |-> C ) = ( x e. B |-> C ) )

  proof
    wph
    cA
    cB
    wceq
    #
    vx
    wal
    cC
    cC
    wceq
    #
    vx
    cA
    wral
    #
    vx
    cA
    cC
    cmpt
    vx
    cB
    cC
    cmpt
    wceq
    wph
    @0
    vx
    mpteq1df.1
    mpteq1df.2
    alrimi
    @2
    wph
    @1
    vx
    cA
    cC
    eqid
    rgenw
    a1i
    vx
    cA
    cC
    cB
    cC
    mpteq12f
    syl2anc
end
