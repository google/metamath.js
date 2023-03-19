include "wcel.mm"
include "caddc.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "co.mm"
include "wceq.mm"
include "00id.mm"
include "a1i.mm"
include "cuz.mm"
include "cfv.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "cv.mm"
include "cfz.mm"
include "wa.mm"
include "cc.mm"
include "0cn.mm"
include "elfzuz.mm"
include "syl6eleqr.mm"
include "adantl.mm"
include "fvconst2g.mm"
include "sylancr.mm"
include "seqid3.mm"

theorem ser0
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vk: setvar k
  assume ser0.1: |- Z = ( ZZ>= ` M )


  assert |- ( N e. Z -> ( seq M ( + , ( Z X. { 0 } ) ) ` N ) = 0 )

  proof
    cN
    cZ
    wcel
    #
    vk
    caddc
    cZ
    cc0
    csn
    cxp
    #
    cM
    cN
    cc0
    cc0
    cc0
    caddc
    co
    cc0
    wceq
    @0
    00id
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
    ser0.1
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
    cc0
    cc
    wcel
    @3
    cZ
    wcel
    #
    @3
    @1
    cfv
    cc0
    wceq
    0cn
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
    ser0.1
    syl6eleqr
    adantl
    cZ
    cc0
    @3
    cc
    fvconst2g
    sylancr
    seqid3
end
