include "cnv.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "c1.mm"
include "c4.mm"
include "cfz.mm"
include "ci.mm"
include "cv.mm"
include "cexp.mm"
include "cns.mm"
include "cfv.mm"
include "cpv.mm"
include "cnmcv.mm"
include "c2.mm"
include "cmul.mm"
include "csu.mm"
include "cdiv.mm"
include "cc.mm"
include "eqid.mm"
include "ipval.mm"
include "fzfid.mm"
include "wa.mm"
include "cn0.mm"
include "ax-icn.mm"
include "elfznn.mm"
include "nnnn0d.mm"
include "expcl.mm"
include "sylancr.mm"
include "adantl.mm"
include "ipval2lem4.mm"
include "sylan2.mm"
include "mulcld.mm"
include "fsumcl.mm"
include "cc0.mm"
include "wne.mm"
include "4cn.mm"
include "4ne0.mm"
include "divcl.mm"
include "mp3an23.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem dipcl
  let cA: class A
  let cB: class B
  let cP: class P
  let cU: class U
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume ipcl.1: |- X = ( BaseSet ` U )
  assume ipcl.7: |- P = ( .iOLD ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( A P B ) e. CC )

  proof
    cU
    cnv
    wcel
    cA
    cX
    wcel
    cB
    cX
    wcel
    w3a
    #
    cA
    cB
    cP
    co
    c1
    c4
    cfz
    co
    #
    ci
    vk
    cv
    #
    cexp
    co
    #
    cA
    @3
    cB
    cU
    cns
    cfv
    #
    co
    cU
    cpv
    cfv
    #
    co
    cU
    cnmcv
    cfv
    #
    cfv
    c2
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    c4
    cdiv
    co
    #
    cc
    cA
    cB
    cP
    @4
    cU
    vk
    @5
    @6
    cX
    ipcl.1
    @5
    eqid
    #
    @4
    eqid
    #
    @6
    eqid
    #
    ipcl.7
    ipval
    @0
    @9
    cc
    wcel
    #
    @10
    cc
    wcel
    #
    @0
    @1
    @8
    vk
    @0
    c1
    c4
    fzfid
    @0
    @2
    @1
    wcel
    #
    wa
    @3
    @7
    @16
    @3
    cc
    wcel
    #
    @0
    @16
    ci
    cc
    wcel
    @2
    cn0
    wcel
    @17
    ax-icn
    @16
    @2
    @2
    c4
    elfznn
    nnnn0d
    ci
    @2
    expcl
    sylancr
    #
    adantl
    @16
    @0
    @17
    @7
    cc
    wcel
    @18
    cA
    cB
    @3
    cP
    @4
    cU
    @5
    @6
    cX
    ipcl.1
    @11
    @12
    @13
    ipcl.7
    ipval2lem4
    sylan2
    mulcld
    fsumcl
    @14
    c4
    cc
    wcel
    c4
    cc0
    wne
    @15
    4cn
    4ne0
    @9
    c4
    divcl
    mp3an23
    syl
    eqeltrd
end
