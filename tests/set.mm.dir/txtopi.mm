include "ctop.mm"
include "wcel.mm"
include "ctx.mm"
include "co.mm"
include "txtop.mm"
include "mp2an.mm"

theorem txtopi
  let cR: class R
  let cS: class S
  assume txtopi.1: |- R e. Top
  assume txtopi.2: |- S e. Top


  assert |- ( R tX S ) e. Top

  proof
    cR
    ctop
    wcel
    cS
    ctop
    wcel
    cR
    cS
    ctx
    co
    ctop
    wcel
    txtopi.1
    txtopi.2
    cR
    cS
    txtop
    mp2an
end
