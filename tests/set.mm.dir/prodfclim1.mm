include "cz.mm"
include "wcel.mm"
include "cmul.mm"
include "c1.mm"
include "csn.mm"
include "cxp.mm"
include "cseq.mm"
include "cli.mm"
include "prodf1f.mm"
include "cc.mm"
include "wbr.mm"
include "ax-1cn.mm"
include "cuz.mm"
include "cfv.mm"
include "eqimss2i.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "climconst2.mm"
include "mpan.mm"
include "eqbrtrd.mm"

theorem prodfclim1
  let cM: class M
  let cZ: class Z
  let vk: setvar k
  let cN: class N
  assume prodf1.1: |- Z = ( ZZ>= ` M )


  assert |- ( M e. ZZ -> seq M ( x. , ( Z X. { 1 } ) ) ~~> 1 )

  proof
    cM
    cz
    wcel
    #
    cmul
    cZ
    c1
    csn
    cxp
    #
    cM
    cseq
    @1
    c1
    cli
    cM
    cZ
    prodf1.1
    prodf1f
    c1
    cc
    wcel
    @0
    @1
    c1
    cli
    wbr
    ax-1cn
    c1
    cM
    cZ
    cZ
    cM
    cuz
    cfv
    #
    prodf1.1
    eqimss2i
    cZ
    @2
    cvv
    prodf1.1
    cM
    cuz
    fvex
    eqeltri
    climconst2
    mpan
    eqbrtrd
end
