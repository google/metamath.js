include "cn0.mm"
include "wcel.mm"
include "csn.mm"
include "c2.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "csu.mm"
include "cbits.mm"
include "cfv.mm"
include "cc.mm"
include "wceq.mm"
include "cn.mm"
include "2nn.mm"
include "a1i.mm"
include "id.mm"
include "nnexpcld.mm"
include "nncnd.mm"
include "oveq2.mm"
include "sumsn.mm"
include "mpdan.mm"
include "fveq2d.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wss.mm"
include "snssi.mm"
include "snfi.mm"
include "elfpw.mm"
include "sylanbrc.mm"
include "bitsinv2.mm"
include "syl.mm"
include "eqtr3d.mm"

theorem 2ebits
  let cN: class N
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let cA: class A
  let vy: setvar y


  assert |- ( N e. NN0 -> ( bits ` ( 2 ^ N ) ) = { N } )

  proof
    cN
    cn0
    wcel
    #
    cN
    csn
    #
    c2
    vk
    cv
    #
    cexp
    co
    #
    vk
    csu
    #
    cbits
    cfv
    #
    c2
    cN
    cexp
    co
    #
    cbits
    cfv
    @1
    @0
    @4
    @6
    cbits
    @0
    @6
    cc
    wcel
    @4
    @6
    wceq
    @0
    @6
    @0
    c2
    cN
    c2
    cn
    wcel
    @0
    2nn
    a1i
    @0
    id
    nnexpcld
    nncnd
    @3
    @6
    vk
    cN
    cn0
    @2
    cN
    c2
    cexp
    oveq2
    sumsn
    mpdan
    fveq2d
    @0
    @1
    cn0
    cpw
    cfn
    cin
    wcel
    #
    @5
    @1
    wceq
    @0
    @1
    cn0
    wss
    @1
    cfn
    wcel
    #
    @7
    cN
    cn0
    snssi
    @8
    @0
    cN
    snfi
    a1i
    @1
    cn0
    elfpw
    sylanbrc
    @1
    vk
    bitsinv2
    syl
    eqtr3d
end
