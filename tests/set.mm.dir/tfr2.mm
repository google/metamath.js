include "con0.mm"
include "wcel.mm"
include "cdm.mm"
include "cfv.mm"
include "cres.mm"
include "wceq.mm"
include "wfn.mm"
include "tfr1.mm"
include "fndm.mm"
include "ax-mp.mm"
include "eleq2i.mm"
include "tfr2a.mm"
include "sylbir.mm"

theorem tfr2
  let cA: class A
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  assume tfr.1: |- F = recs ( G )


  assert |- ( A e. On -> ( F ` A ) = ( G ` ( F |` A ) ) )

  proof
    cA
    con0
    wcel
    cA
    cF
    cdm
    #
    wcel
    cA
    cF
    cfv
    cF
    cA
    cres
    cG
    cfv
    wceq
    @0
    con0
    cA
    cF
    con0
    wfn
    @0
    con0
    wceq
    cF
    cG
    tfr.1
    tfr1
    con0
    cF
    fndm
    ax-mp
    eleq2i
    cA
    cF
    cG
    tfr.1
    tfr2a
    sylbir
end
