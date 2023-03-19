include "cc0.mm"
include "csn.mm"
include "cun.mm"
include "cply.mm"
include "cfv.mm"
include "cc.mm"
include "wss.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "wceq.mm"
include "cn0.mm"
include "cmap.mm"
include "wrex.mm"
include "wa.mm"
include "wcel.mm"
include "0cn.mm"
include "snssi.mm"
include "ax-mp.mm"
include "biantru.mm"
include "unss.mm"
include "bitr2i.mm"
include "unass.mm"
include "unidm.mm"
include "uneq2i.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "rexeqi.mm"
include "rexbii.mm"
include "anbi12i.mm"
include "elply.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem plyun0
  let cS: class S
  let va: setvar a
  let vk: setvar k
  let vn: setvar n
  let vz: setvar z
  let cA: class A
  let cN: class N
  let vf: setvar f
  let vx: setvar x
  let cT: class T
  let cF: class F


  assert |- ( Poly ` ( S u. { 0 } ) ) = ( Poly ` S )

  proof
    vf
    cS
    cc0
    csn
    #
    cun
    #
    cply
    cfv
    #
    cS
    cply
    cfv
    #
    @1
    cc
    wss
    #
    vf
    cv
    #
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
    @6
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
    @1
    @0
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
    wa
    cS
    cc
    wss
    #
    @7
    va
    @1
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
    wa
    @5
    @2
    wcel
    @5
    @3
    wcel
    @4
    @12
    @11
    @15
    @12
    @12
    @0
    cc
    wss
    #
    wa
    @4
    @16
    @12
    cc0
    cc
    wcel
    @16
    0cn
    cc0
    cc
    snssi
    ax-mp
    biantru
    cS
    @0
    cc
    unss
    bitr2i
    @10
    @14
    vn
    cn0
    @7
    va
    @9
    @13
    @8
    @1
    cn0
    cmap
    @8
    cS
    @0
    @0
    cun
    #
    cun
    @1
    cS
    @0
    @0
    unass
    @17
    @0
    cS
    @0
    unidm
    uneq2i
    eqtri
    oveq1i
    rexeqi
    rexbii
    anbi12i
    vz
    @1
    vk
    vn
    @5
    va
    elply
    vz
    cS
    vk
    vn
    @5
    va
    elply
    3bitr4i
    eqriv
end
