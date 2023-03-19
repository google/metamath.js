include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cre.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "ccj.mm"
include "caddc.mm"
include "cdiv.mm"
include "reval.mm"
include "oveq2d.mm"
include "wceq.mm"
include "cjcl.mm"
include "addcl.mm"
include "mpdan.mm"
include "cc0.mm"
include "wne.mm"
include "2cn.mm"
include "2ne0.mm"
include "divcan2.mm"
include "mp3an23.mm"
include "syl.mm"
include "eqtr2d.mm"

theorem addcj
  let cA: class A


  assert |- ( A e. CC -> ( A + ( * ` A ) ) = ( 2 x. ( Re ` A ) ) )

  proof
    cA
    cc
    wcel
    #
    c2
    cA
    cre
    cfv
    #
    cmul
    co
    c2
    cA
    cA
    ccj
    cfv
    #
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cmul
    co
    #
    @3
    @0
    @1
    @4
    c2
    cmul
    cA
    reval
    oveq2d
    @0
    @3
    cc
    wcel
    #
    @5
    @3
    wceq
    #
    @0
    @2
    cc
    wcel
    @6
    cA
    cjcl
    cA
    @2
    addcl
    mpdan
    @6
    c2
    cc
    wcel
    c2
    cc0
    wne
    @7
    2cn
    2ne0
    @3
    c2
    divcan2
    mp3an23
    syl
    eqtr2d
end
