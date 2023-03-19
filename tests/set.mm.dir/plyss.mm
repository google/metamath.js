include "wss.mm"
include "cc.mm"
include "wa.mm"
include "cv.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cfv.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "wceq.mm"
include "csn.mm"
include "cun.mm"
include "cn0.mm"
include "cmap.mm"
include "wrex.mm"
include "cab.mm"
include "cply.mm"
include "wi.mm"
include "cvv.mm"
include "wcel.mm"
include "simpr.mm"
include "cnex.mm"
include "ssexg.mm"
include "sylancl.mm"
include "snex.mm"
include "unexg.mm"
include "unss1.mm"
include "adantr.mm"
include "mapss.mm"
include "syl2anc.mm"
include "ssrexv.mm"
include "syl.mm"
include "reximdv.mm"
include "ss2abdv.mm"
include "sstr.mm"
include "plyval.mm"
include "adantl.mm"
include "3sstr4d.mm"

theorem plyss
  let cS: class S
  let cT: class T
  let va: setvar a
  let vk: setvar k
  let vn: setvar n
  let vz: setvar z
  let cA: class A
  let cN: class N
  let vf: setvar f
  let vx: setvar x
  let cF: class F


  assert |- ( ( S C_ T /\ T C_ CC ) -> ( Poly ` S ) C_ ( Poly ` T ) )

  proof
    cS
    cT
    wss
    #
    cT
    cc
    wss
    #
    wa
    #
    vf
    cv
    vz
    cc
    cc0
    vn
    cv
    cfz
    co
    vk
    cv
    #
    va
    cv
    cfv
    vz
    cv
    @3
    cexp
    co
    cmul
    co
    vk
    csu
    cmpt
    wceq
    #
    va
    cS
    cc0
    csn
    #
    cun
    #
    cn0
    cmap
    co
    #
    wrex
    #
    vn
    cn0
    wrex
    #
    vf
    cab
    #
    @4
    va
    cT
    @5
    cun
    #
    cn0
    cmap
    co
    #
    wrex
    #
    vn
    cn0
    wrex
    #
    vf
    cab
    #
    cS
    cply
    cfv
    #
    cT
    cply
    cfv
    #
    @2
    @9
    @14
    vf
    @2
    @8
    @13
    vn
    cn0
    @2
    @7
    @12
    wss
    #
    @8
    @13
    wi
    @2
    @11
    cvv
    wcel
    #
    @6
    @11
    wss
    #
    @18
    @2
    cT
    cvv
    wcel
    #
    @5
    cvv
    wcel
    @19
    @2
    @1
    cc
    cvv
    wcel
    @21
    @0
    @1
    simpr
    cnex
    cT
    cc
    cvv
    ssexg
    sylancl
    cc0
    snex
    cT
    @5
    cvv
    cvv
    unexg
    sylancl
    @0
    @20
    @1
    cS
    cT
    @5
    unss1
    adantr
    @6
    @11
    cn0
    cvv
    mapss
    syl2anc
    @4
    va
    @7
    @12
    ssrexv
    syl
    reximdv
    ss2abdv
    @2
    cS
    cc
    wss
    @16
    @10
    wceq
    cS
    cT
    cc
    sstr
    vz
    cS
    vf
    vk
    vn
    va
    plyval
    syl
    @1
    @17
    @15
    wceq
    @0
    vz
    cT
    vf
    vk
    vn
    va
    plyval
    adantl
    3sstr4d
end
