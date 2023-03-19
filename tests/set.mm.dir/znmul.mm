include "cmulr.mm"
include "c3.mm"
include "df-mulr.mm"
include "3nn.mm"
include "3lt10.mm"
include "znbaslem.mm"

theorem znmul
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


  assert |- ( N e. NN0 -> ( .r ` U ) = ( .r ` Y ) )

  proof
    cS
    cU
    cmulr
    c3
    cN
    cY
    znval2.s
    znval2.u
    znval2.y
    df-mulr
    3nn
    3lt10
    znbaslem
end
