include "wceq.mm"
include "wal.mm"
include "wral.mm"
include "cmpt.mm"
include "eqid.mm"
include "ax-gen.mm"
include "rgen.mm"
include "mpteq12f.mm"
include "mp2an.mm"

theorem mpteq2ia
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume mpteq2ia.1: |- ( x e. A -> B = C )


  assert |- ( x e. A |-> B ) = ( x e. A |-> C )

  proof
    cA
    cA
    wceq
    #
    vx
    wal
    cB
    cC
    wceq
    #
    vx
    cA
    wral
    vx
    cA
    cB
    cmpt
    vx
    cA
    cC
    cmpt
    wceq
    @0
    vx
    cA
    eqid
    ax-gen
    @1
    vx
    cA
    mpteq2ia.1
    rgen
    vx
    cA
    cB
    cA
    cC
    mpteq12f
    mp2an
end
