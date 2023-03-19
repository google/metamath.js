include "wbr.mm"
include "wa.mm"
include "soirri.mm"
include "sotri.mm"
include "mto.mm"

theorem son2lpi
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  assume soi.1: |- R Or S
  assume soi.2: |- R C_ ( S X. S )


  assert |- -. ( A R B /\ B R A )

  proof
    cA
    cB
    cR
    wbr
    cB
    cA
    cR
    wbr
    wa
    cA
    cA
    cR
    wbr
    cA
    cR
    cS
    soi.1
    soi.2
    soirri
    cA
    cB
    cA
    cR
    cS
    soi.1
    soi.2
    sotri
    mto
end
