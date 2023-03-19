include "cple.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "df-ple.mm"
include "10nn.mm"
include "1lt10.mm"
include "resslem.mm"

theorem ressle
  let cA: class A
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  assume ressle.1: |- W = ( K |`s A )
  assume ressle.2: |- .<_ = ( le ` K )


  assert |- ( A e. V -> .<_ = ( le ` W ) )

  proof
    cA
    c.le
    cW
    cple
    c1
    cc0
    cdc
    cV
    cK
    ressle.1
    ressle.2
    df-ple
    10nn
    1lt10
    resslem
end
