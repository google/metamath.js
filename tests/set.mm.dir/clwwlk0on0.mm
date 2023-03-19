include "cvtx.mm"
include "cfv.mm"
include "wcel.mm"
include "cc0.mm"
include "cn0.mm"
include "wa.mm"
include "cclwwlknon.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "crab.mm"
include "cclwwlkn.mm"
include "eqeq2.mm"
include "rabbidv.mm"
include "oveq1.mm"
include "clwwlkn0.mm"
include "syl6eq.mm"
include "rabeqdv.mm"
include "clwwlknonmpt2.mm"
include "0ex.mm"
include "rabex.mm"
include "ovmpt2.mm"
include "rab0.mm"
include "mpt2ndm0.mm"
include "pm2.61i.mm"

theorem clwwlk0on0
  let cG: class G
  let cX: class X
  let vn: setvar n
  let vv: setvar v
  let vw: setvar w


  assert |- ( X ( ClWWalksNOn ` G ) 0 ) = (/)

  proof
    cX
    cG
    cvtx
    cfv
    #
    wcel
    cc0
    cn0
    wcel
    wa
    #
    cX
    cc0
    cG
    cclwwlknon
    cfv
    #
    co
    #
    c0
    wceq
    @1
    @3
    cc0
    vw
    cv
    cfv
    #
    cX
    wceq
    #
    vw
    c0
    crab
    #
    c0
    vv
    vn
    cX
    cc0
    @0
    cn0
    @4
    vv
    cv
    #
    wceq
    #
    vw
    vn
    cv
    #
    cG
    cclwwlkn
    co
    #
    crab
    #
    @6
    @2
    @5
    vw
    @10
    crab
    @7
    cX
    wceq
    @8
    @5
    vw
    @10
    @7
    cX
    @4
    eqeq2
    rabbidv
    @9
    cc0
    wceq
    #
    @5
    vw
    @10
    c0
    @12
    @10
    cc0
    cG
    cclwwlkn
    co
    c0
    @9
    cc0
    cG
    cclwwlkn
    oveq1
    cG
    clwwlkn0
    syl6eq
    rabeqdv
    vw
    vv
    vn
    cG
    clwwlknonmpt2
    #
    @5
    vw
    c0
    0ex
    rabex
    ovmpt2
    @5
    vw
    rab0
    syl6eq
    vv
    vn
    @11
    @2
    cX
    cc0
    @0
    cn0
    @13
    mpt2ndm0
    pm2.61i
end
