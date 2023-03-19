include "wceq.mm"
include "cwsuc.mm"
include "eqid.mm"
include "wsuceq123.mm"
include "mp3an23.mm"

theorem wsuceq1
  let cA: class A
  let cR: class R
  let cS: class S
  let cX: class X


  assert |- ( R = S -> wsuc ( R , A , X ) = wsuc ( S , A , X ) )

  proof
    cR
    cS
    wceq
    cA
    cA
    wceq
    cX
    cX
    wceq
    cA
    cR
    cX
    cwsuc
    cA
    cS
    cX
    cwsuc
    wceq
    cA
    eqid
    cX
    eqid
    cA
    cA
    cR
    cS
    cX
    cX
    wsuceq123
    mp3an23
end
