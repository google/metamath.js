include "cbs.mm"
include "c1.mm"
include "df-base.mm"
include "1nn.mm"
include "1lt10.mm"
include "znbaslem.mm"

theorem znbas2
  let cS: class S
  let cU: class U
  let cN: class N
  let cY: class Y
  let cE: class E
  let vx: setvar x
  let cK: class K
  let vy: setvar y
  assume znval2.s: |- S = ( RSpan ` ZZring )
  assume znval2.u: |- U = ( ZZring /s ( ZZring ~QG ( S ` { N } ) ) )
  assume znval2.y: |- Y = ( Z/nZ ` N )


  assert |- ( N e. NN0 -> ( Base ` U ) = ( Base ` Y ) )

  proof
    cS
    cU
    cbs
    c1
    cN
    cY
    znval2.s
    znval2.u
    znval2.y
    df-base
    1nn
    1lt10
    znbaslem
end
