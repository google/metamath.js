include "wceq.mm"
include "cwlim.mm"
include "eqid.mm"
include "wlimeq12.mm"
include "mpan2.mm"

theorem wlimeq1
  let cA: class A
  let cR: class R
  let cS: class S


  assert |- ( R = S -> WLim ( R , A ) = WLim ( S , A ) )

  proof
    cR
    cS
    wceq
    cA
    cA
    wceq
    cA
    cR
    cwlim
    cA
    cS
    cwlim
    wceq
    cA
    eqid
    cA
    cA
    cR
    cS
    wlimeq12
    mpan2
end
