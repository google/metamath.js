include "wbr.mm"
include "cec.mm"
include "wceq.mm"
include "ercl.mm"
include "erth.mm"
include "mpbid.mm"

theorem erthi
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X
  assume erthi.1: |- ( ph -> R Er X )
  assume erthi.2: |- ( ph -> A R B )


  assert |- ( ph -> [ A ] R = [ B ] R )

  proof
    wph
    cA
    cB
    cR
    wbr
    cA
    cR
    cec
    cB
    cR
    cec
    wceq
    erthi.2
    wph
    cA
    cB
    cR
    cX
    erthi.1
    wph
    cA
    cB
    cR
    cX
    erthi.1
    erthi.2
    ercl
    erth
    mpbid
end
