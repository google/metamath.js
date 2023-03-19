include "wceq.mm"
include "cwlim.mm"
include "eqid.mm"
include "wlimeq12.mm"
include "mpan.mm"

theorem wlimeq2
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( A = B -> WLim ( R , A ) = WLim ( R , B ) )

  proof
    cR
    cR
    wceq
    cA
    cB
    wceq
    cA
    cR
    cwlim
    cB
    cR
    cwlim
    wceq
    cR
    eqid
    cA
    cB
    cR
    cR
    wlimeq12
    mpan
end
