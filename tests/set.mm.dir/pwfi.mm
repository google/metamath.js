include "cfn.mm"
include "wcel.mm"
include "cpw.mm"
include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "com.mm"
include "wrex.mm"
include "isfi.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "pweq.mm"
include "eleq1d.mm"
include "csuc.mm"
include "df-suc.mm"
include "pweqi.mm"
include "syl6eq.mm"
include "c1o.mm"
include "pw0.mm"
include "df1o2.mm"
include "eqtr4i.mm"
include "wss.mm"
include "1onn.mm"
include "ssid.mm"
include "ssnnfi.mm"
include "mp2an.mm"
include "eqeltri.mm"
include "wi.mm"
include "cmpt.mm"
include "eqid.mm"
include "pwfilem.mm"
include "a1i.mm"
include "finds1.mm"
include "pwen.mm"
include "enfii.mm"
include "syl2an.mm"
include "rexlimiva.mm"
include "sylbi.mm"
include "cdom.mm"
include "cvv.mm"
include "csdm.mm"
include "pwexr.mm"
include "canth2g.mm"
include "sdomdom.mm"
include "3syl.mm"
include "domfi.mm"
include "mpdan.mm"
include "impbii.mm"

theorem pwfi
  let cA: class A
  let vm: setvar m
  let vc: setvar c
  let vk: setvar k


  assert |- ( A e. Fin <-> ~P A e. Fin )

  proof
    cA
    cfn
    wcel
    #
    cA
    cpw
    #
    cfn
    wcel
    #
    @0
    cA
    vm
    cv
    #
    cen
    wbr
    #
    vm
    com
    wrex
    @2
    vm
    cA
    isfi
    @4
    @2
    vm
    com
    @3
    com
    wcel
    @3
    cpw
    #
    cfn
    wcel
    #
    @1
    @5
    cen
    wbr
    @2
    @4
    @6
    c0
    cpw
    #
    cfn
    wcel
    vk
    cv
    #
    cpw
    #
    cfn
    wcel
    #
    @8
    @8
    csn
    #
    cun
    #
    cpw
    #
    cfn
    wcel
    #
    vm
    vk
    @3
    c0
    wceq
    @5
    @7
    cfn
    @3
    c0
    pweq
    eleq1d
    @3
    @8
    wceq
    @5
    @9
    cfn
    @3
    @8
    pweq
    eleq1d
    @3
    @8
    csuc
    #
    wceq
    #
    @5
    @13
    cfn
    @16
    @5
    @15
    cpw
    @13
    @3
    @15
    pweq
    @15
    @12
    @8
    df-suc
    pweqi
    syl6eq
    eleq1d
    @7
    c1o
    cfn
    @7
    c0
    csn
    c1o
    pw0
    df1o2
    eqtr4i
    c1o
    com
    wcel
    c1o
    c1o
    wss
    c1o
    cfn
    wcel
    1onn
    c1o
    ssid
    c1o
    c1o
    ssnnfi
    mp2an
    eqeltri
    @10
    @14
    wi
    @8
    com
    wcel
    vk
    vc
    @9
    vc
    cv
    @11
    cun
    cmpt
    #
    vk
    vc
    @17
    eqid
    pwfilem
    a1i
    finds1
    cA
    @3
    pwen
    @1
    @5
    enfii
    syl2an
    rexlimiva
    sylbi
    @2
    cA
    @1
    cdom
    wbr
    #
    @0
    @2
    cA
    cvv
    wcel
    cA
    @1
    csdm
    wbr
    @18
    cA
    cfn
    pwexr
    cA
    cvv
    canth2g
    cA
    @1
    sdomdom
    3syl
    @1
    cA
    domfi
    mpdan
    impbii
end
