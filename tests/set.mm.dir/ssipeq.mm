include "wcel.mm"
include "cip.mm"
include "cfv.mm"
include "ressip.mm"
include "syl6reqr.mm"

theorem ssipeq
  let cP: class P
  let cS: class S
  let cU: class U
  let c.xi: class .,
  let cW: class W
  let cX: class X
  assume ssipeq.x: |- X = ( W |`s U )
  assume ssipeq.i: |- ., = ( .i ` W )
  assume ssipeq.p: |- P = ( .i ` X )


  assert |- ( U e. S -> P = ., )

  proof
    cU
    cS
    wcel
    c.xi
    cX
    cip
    cfv
    cP
    cU
    cW
    cX
    c.xi
    cS
    ssipeq.x
    ssipeq.i
    ressip
    ssipeq.p
    syl6reqr
end
