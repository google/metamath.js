include "cn0.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "eqidd.mm"
include "znbas2.mm"
include "cv.mm"
include "wa.mm"
include "cplusg.mm"
include "znadd.mm"
include "oveqdr.mm"
include "cmulr.mm"
include "znmul.mm"
include "zrhpropd.mm"

theorem znzrh
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


  assert |- ( N e. NN0 -> ( ZRHom ` U ) = ( ZRHom ` Y ) )

  proof
    cN
    cn0
    wcel
    #
    vx
    vy
    cU
    cbs
    cfv
    #
    cU
    cY
    @0
    @1
    eqidd
    cS
    cU
    cN
    cY
    znval2.s
    znval2.u
    znval2.y
    znbas2
    @0
    vx
    cv
    @1
    wcel
    vy
    cv
    @1
    wcel
    wa
    #
    vx
    vy
    cU
    cplusg
    cfv
    cY
    cplusg
    cfv
    cS
    cU
    cN
    cY
    znval2.s
    znval2.u
    znval2.y
    znadd
    oveqdr
    @0
    @2
    vx
    vy
    cU
    cmulr
    cfv
    cY
    cmulr
    cfv
    cS
    cU
    cN
    cY
    znval2.s
    znval2.u
    znval2.y
    znmul
    oveqdr
    zrhpropd
end
