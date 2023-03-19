include "cvtx.mm"
include "cfv.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "wn.mm"
include "cclwwlknon.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "wi.mm"
include "cc0.mm"
include "oveq2.mm"
include "clwwlk0on0.mm"
include "syl6eq.mm"
include "a1d.mm"
include "wne.mm"
include "cn0.mm"
include "simprl.mm"
include "elnnne0.mm"
include "simplbi2.mm"
include "adantl.mm"
include "impcom.mm"
include "jca.mm"
include "stoic1a.mm"
include "cv.mm"
include "cclwwlkn.mm"
include "crab.mm"
include "clwwlknonmpt2.mm"
include "mpt2ndm0.mm"
include "syl.mm"
include "ex.mm"
include "pm2.61ine.mm"

theorem clwwlknon0
  let cG: class G
  let cN: class N
  let cX: class X
  let vn: setvar n
  let vv: setvar v
  let vw: setvar w


  assert |- ( -. ( X e. ( Vtx ` G ) /\ N e. NN ) -> ( X ( ClWWalksNOn ` G ) N ) = (/) )

  proof
    cX
    cG
    cvtx
    cfv
    #
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    wn
    #
    cX
    cN
    cG
    cclwwlknon
    cfv
    #
    co
    #
    c0
    wceq
    #
    wi
    cN
    cc0
    cN
    cc0
    wceq
    #
    @7
    @4
    @8
    @6
    cX
    cc0
    @5
    co
    c0
    cN
    cc0
    cX
    @5
    oveq2
    cG
    cX
    clwwlk0on0
    syl6eq
    a1d
    cN
    cc0
    wne
    #
    @4
    @7
    @9
    @4
    wa
    @1
    cN
    cn0
    wcel
    #
    wa
    #
    wn
    @7
    @9
    @11
    @3
    @9
    @11
    wa
    @1
    @2
    @9
    @1
    @10
    simprl
    @11
    @9
    @2
    @10
    @9
    @2
    wi
    @1
    @2
    @10
    @9
    cN
    elnnne0
    simplbi2
    adantl
    impcom
    jca
    stoic1a
    vv
    vn
    cc0
    vw
    cv
    cfv
    vv
    cv
    wceq
    vw
    vn
    cv
    cG
    cclwwlkn
    co
    crab
    @5
    cX
    cN
    @0
    cn0
    vw
    vv
    vn
    cG
    clwwlknonmpt2
    mpt2ndm0
    syl
    ex
    pm2.61ine
end
