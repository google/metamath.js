include "cplusg.mm"
include "c2.mm"
include "df-plusg.mm"
include "2nn.mm"
include "2lt10.mm"
include "znbaslem.mm"

theorem znadd
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


  assert |- ( N e. NN0 -> ( +g ` U ) = ( +g ` Y ) )

  proof
    cS
    cU
    cplusg
    c2
    cN
    cY
    znval2.s
    znval2.u
    znval2.y
    df-plusg
    2nn
    2lt10
    znbaslem
end
