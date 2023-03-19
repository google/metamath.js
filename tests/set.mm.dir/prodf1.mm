include "wcel.mm"
include "cmul.mm"
include "c1.mm"
include "csn.mm"
include "cxp.mm"
include "co.mm"
include "wceq.mm"
include "1t1e1.mm"
include "a1i.mm"
include "cuz.mm"
include "cfv.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "cv.mm"
include "cfz.mm"
include "wa.mm"
include "cc.mm"
include "ax-1cn.mm"
include "elfzuz.mm"
include "syl6eleqr.mm"
include "adantl.mm"
include "fvconst2g.mm"
include "sylancr.mm"
include "seqid3.mm"

theorem prodf1
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vk: setvar k
  assume prodf1.1: |- Z = ( ZZ>= ` M )


  assert |- ( N e. Z -> ( seq M ( x. , ( Z X. { 1 } ) ) ` N ) = 1 )

  proof
    cN
    cZ
    wcel
    #
    vk
    cmul
    cZ
    c1
    csn
    cxp
    #
    cM
    cN
    c1
    c1
    c1
    cmul
    co
    c1
    wceq
    @0
    1t1e1
    a1i
    @0
    cN
    cM
    cuz
    cfv
    #
    wcel
    cZ
    @2
    cN
    prodf1.1
    eleq2i
    biimpi
    @0
    vk
    cv
    #
    cM
    cN
    cfz
    co
    wcel
    #
    wa
    c1
    cc
    wcel
    @3
    cZ
    wcel
    #
    @3
    @1
    cfv
    c1
    wceq
    ax-1cn
    @4
    @5
    @0
    @4
    @3
    @2
    cZ
    @3
    cM
    cN
    elfzuz
    prodf1.1
    syl6eleqr
    adantl
    cZ
    c1
    @3
    cc
    fvconst2g
    sylancr
    seqid3
end
