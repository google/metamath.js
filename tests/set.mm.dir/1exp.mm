include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "cexp.mm"
include "co.mm"
include "csn.mm"
include "wceq.mm"
include "cc0.mm"
include "wne.mm"
include "1ex.mm"
include "snid.mm"
include "ax-1ne0.mm"
include "cc.mm"
include "wss.mm"
include "ax-1cn.mm"
include "snssi.mm"
include "ax-mp.mm"
include "cv.mm"
include "wa.mm"
include "cmul.mm"
include "elsni.mm"
include "oveq12.mm"
include "1t1e1.mm"
include "syl6eq.mm"
include "syl2an.mm"
include "ovex.mm"
include "elsn.mm"
include "sylibr.mm"
include "cdiv.mm"
include "oveq2d.mm"
include "1div1e1.mm"
include "adantr.mm"
include "expcl2lem.mm"
include "mp3an12.mm"
include "syl.mm"

theorem 1exp
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let vj: setvar j
  let vk: setvar k
  let cA: class A


  assert |- ( N e. ZZ -> ( 1 ^ N ) = 1 )

  proof
    cN
    cz
    wcel
    #
    c1
    cN
    cexp
    co
    #
    c1
    csn
    #
    wcel
    #
    @1
    c1
    wceq
    c1
    @2
    wcel
    c1
    cc0
    wne
    @0
    @3
    c1
    1ex
    snid
    #
    ax-1ne0
    vx
    vy
    c1
    cN
    @2
    c1
    cc
    wcel
    @2
    cc
    wss
    ax-1cn
    c1
    cc
    snssi
    ax-mp
    vx
    cv
    #
    @2
    wcel
    #
    vy
    cv
    #
    @2
    wcel
    #
    wa
    @5
    @7
    cmul
    co
    #
    c1
    wceq
    #
    @9
    @2
    wcel
    @6
    @5
    c1
    wceq
    #
    @7
    c1
    wceq
    #
    @10
    @8
    @5
    c1
    elsni
    #
    @7
    c1
    elsni
    @11
    @12
    wa
    @9
    c1
    c1
    cmul
    co
    c1
    @5
    c1
    @7
    c1
    cmul
    oveq12
    1t1e1
    syl6eq
    syl2an
    @9
    c1
    @5
    @7
    cmul
    ovex
    elsn
    sylibr
    @4
    @6
    c1
    @5
    cdiv
    co
    #
    @2
    wcel
    #
    @5
    cc0
    wne
    @6
    @14
    c1
    wceq
    @15
    @6
    @14
    c1
    c1
    cdiv
    co
    c1
    @6
    @5
    c1
    c1
    cdiv
    @13
    oveq2d
    1div1e1
    syl6eq
    @14
    c1
    c1
    @5
    cdiv
    ovex
    elsn
    sylibr
    adantr
    expcl2lem
    mp3an12
    @1
    c1
    elsni
    syl
end
