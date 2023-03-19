include "cc.mm"
include "wcel.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cc0.mm"
include "wceq.mm"
include "cv.mm"
include "wrex.mm"
include "ax-icn.mm"
include "mulcli.mm"
include "mulcl.mm"
include "mpan.mm"
include "c1.mm"
include "mulid2.mm"
include "oveq2d.mm"
include "ax-i2m1.mm"
include "oveq1i.mm"
include "ax-1cn.mm"
include "adddir.mm"
include "mp3an12.mm"
include "mul02.mm"
include "3eqtr3a.mm"
include "eqtr3d.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"

theorem cnegex2
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A e. CC -> E. x e. CC ( x + A ) = 0 )

  proof
    cA
    cc
    wcel
    #
    ci
    ci
    cmul
    co
    #
    cA
    cmul
    co
    #
    cc
    wcel
    #
    @2
    cA
    caddc
    co
    #
    cc0
    wceq
    #
    vx
    cv
    #
    cA
    caddc
    co
    #
    cc0
    wceq
    #
    vx
    cc
    wrex
    @1
    cc
    wcel
    #
    @0
    @3
    ci
    ci
    ax-icn
    ax-icn
    mulcli
    #
    @1
    cA
    mulcl
    mpan
    @0
    @2
    c1
    cA
    cmul
    co
    #
    caddc
    co
    #
    @4
    cc0
    @0
    @11
    cA
    @2
    caddc
    cA
    mulid2
    oveq2d
    @0
    @1
    c1
    caddc
    co
    #
    cA
    cmul
    co
    #
    cc0
    cA
    cmul
    co
    @12
    cc0
    @13
    cc0
    cA
    cmul
    ax-i2m1
    oveq1i
    @9
    c1
    cc
    wcel
    @0
    @14
    @12
    wceq
    @10
    ax-1cn
    @1
    c1
    cA
    adddir
    mp3an12
    cA
    mul02
    3eqtr3a
    eqtr3d
    @8
    @5
    vx
    @2
    cc
    @6
    @2
    wceq
    @7
    @4
    cc0
    @6
    @2
    cA
    caddc
    oveq1
    eqeq1d
    rspcev
    syl2anc
end
