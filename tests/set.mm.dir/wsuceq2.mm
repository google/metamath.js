include "wceq.mm"
include "cwsuc.mm"
include "eqid.mm"
include "wsuceq123.mm"
include "mp3an13.mm"

theorem wsuceq2
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X


  assert |- ( A = B -> wsuc ( R , A , X ) = wsuc ( R , B , X ) )

  proof
    cR
    cR
    wceq
    cA
    cB
    wceq
    cX
    cX
    wceq
    cA
    cR
    cX
    cwsuc
    cB
    cR
    cX
    cwsuc
    wceq
    cR
    eqid
    cX
    eqid
    cA
    cB
    cR
    cR
    cX
    cX
    wsuceq123
    mp3an13
end
