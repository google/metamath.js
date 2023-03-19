include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "caddc.mm"
include "cen.mm"
include "wbr.mm"
include "peano2zm.mm"
include "0z.mm"
include "1z.mm"
include "fzen.mm"
include "mp3an13.mm"
include "syl.mm"
include "wceq.mm"
include "0p1e1.mm"
include "a1i.mm"
include "cc.mm"
include "zcn.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "oveq12d.mm"
include "breqtrd.mm"

theorem fz01en
  let cN: class N


  assert |- ( N e. ZZ -> ( 0 ... ( N - 1 ) ) ~~ ( 1 ... N ) )

  proof
    cN
    cz
    wcel
    #
    cc0
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    cc0
    c1
    caddc
    co
    #
    @1
    c1
    caddc
    co
    #
    cfz
    co
    #
    c1
    cN
    cfz
    co
    cen
    @0
    @1
    cz
    wcel
    #
    @2
    @5
    cen
    wbr
    #
    cN
    peano2zm
    cc0
    cz
    wcel
    @6
    c1
    cz
    wcel
    @7
    0z
    1z
    c1
    cc0
    @1
    fzen
    mp3an13
    syl
    @0
    @3
    c1
    @4
    cN
    cfz
    @3
    c1
    wceq
    @0
    0p1e1
    a1i
    @0
    cN
    cc
    wcel
    c1
    cc
    wcel
    @4
    cN
    wceq
    cN
    zcn
    ax-1cn
    cN
    c1
    npcan
    sylancl
    oveq12d
    breqtrd
end
