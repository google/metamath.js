include "ctop.mm"
include "wcel.mm"
include "cxp.mm"
include "ctx.mm"
include "co.mm"
include "cuni.mm"
include "wceq.mm"
include "txuni.mm"
include "mp2an.mm"

theorem txunii
  let cR: class R
  let cS: class S
  let cX: class X
  let cY: class Y
  assume txunii.1: |- R e. Top
  assume txunii.2: |- S e. Top
  assume txunii.3: |- X = U. R
  assume txunii.4: |- Y = U. S


  assert |- ( X X. Y ) = U. ( R tX S )

  proof
    cR
    ctop
    wcel
    cS
    ctop
    wcel
    cX
    cY
    cxp
    cR
    cS
    ctx
    co
    cuni
    wceq
    txunii.1
    txunii.2
    cR
    cS
    cX
    cY
    txunii.3
    txunii.4
    txuni
    mp2an
end
