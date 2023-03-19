include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "cmul.mm"
include "caddc.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "1z.mm"
include "0z.mm"
include "gcdaddm.mm"
include "mp3an13.mm"
include "gcdid0.mm"
include "cc.mm"
include "zcn.mm"
include "mulid2.mm"
include "oveq2d.mm"
include "addid2.mm"
include "eqtrd.mm"
include "syl.mm"
include "3eqtr3rd.mm"

theorem gcdid
  let cN: class N


  assert |- ( N e. ZZ -> ( N gcd N ) = ( abs ` N ) )

  proof
    cN
    cz
    wcel
    #
    cN
    cc0
    cgcd
    co
    #
    cN
    cc0
    c1
    cN
    cmul
    co
    #
    caddc
    co
    #
    cgcd
    co
    #
    cN
    cabs
    cfv
    cN
    cN
    cgcd
    co
    c1
    cz
    wcel
    @0
    cc0
    cz
    wcel
    @1
    @4
    wceq
    1z
    0z
    c1
    cN
    cc0
    gcdaddm
    mp3an13
    cN
    gcdid0
    @0
    @3
    cN
    cN
    cgcd
    @0
    cN
    cc
    wcel
    #
    @3
    cN
    wceq
    cN
    zcn
    @5
    @3
    cc0
    cN
    caddc
    co
    cN
    @5
    @2
    cN
    cc0
    caddc
    cN
    mulid2
    oveq2d
    cN
    addid2
    eqtrd
    syl
    oveq2d
    3eqtr3rd
end
