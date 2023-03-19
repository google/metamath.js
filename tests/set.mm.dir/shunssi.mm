include "cun.mm"
include "cph.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "wo.mm"
include "cva.mm"
include "wceq.mm"
include "wrex.mm"
include "c0v.mm"
include "chil.mm"
include "sheli.mm"
include "ax-hvaddid.mm"
include "eqcomd.mm"
include "syl.mm"
include "csh.mm"
include "sh0.mm"
include "ax-mp.mm"
include "rspceov.mm"
include "mp3an2.mm"
include "mpdan.mm"
include "hvaddid2.mm"
include "mp3an1.mm"
include "jaoi.mm"
include "elun.mm"
include "shseli.mm"
include "3imtr4i.mm"
include "ssriv.mm"

theorem shunssi
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D
  assume shincl.1: |- A e. SH
  assume shincl.2: |- B e. SH


  assert |- ( A u. B ) C_ ( A +H B )

  proof
    vx
    cA
    cB
    cun
    #
    cA
    cB
    cph
    co
    #
    vx
    cv
    #
    cA
    wcel
    #
    @2
    cB
    wcel
    #
    wo
    @2
    vy
    cv
    vz
    cv
    cva
    co
    wceq
    vz
    cB
    wrex
    vy
    cA
    wrex
    #
    @2
    @0
    wcel
    @2
    @1
    wcel
    @3
    @5
    @4
    @3
    @2
    @2
    c0v
    cva
    co
    #
    wceq
    #
    @5
    @3
    @2
    chil
    wcel
    #
    @7
    @2
    cA
    shincl.1
    sheli
    @8
    @6
    @2
    @2
    ax-hvaddid
    eqcomd
    syl
    @3
    c0v
    cB
    wcel
    #
    @7
    @5
    cB
    csh
    wcel
    @9
    shincl.2
    cB
    sh0
    ax-mp
    vy
    vz
    cA
    cB
    @2
    c0v
    @2
    cva
    rspceov
    mp3an2
    mpdan
    @4
    @2
    c0v
    @2
    cva
    co
    #
    wceq
    #
    @5
    @4
    @8
    @11
    @2
    cB
    shincl.2
    sheli
    @8
    @10
    @2
    @2
    hvaddid2
    eqcomd
    syl
    c0v
    cA
    wcel
    #
    @4
    @11
    @5
    cA
    csh
    wcel
    @12
    shincl.1
    cA
    sh0
    ax-mp
    vy
    vz
    cA
    cB
    c0v
    @2
    @2
    cva
    rspceov
    mp3an1
    mpdan
    jaoi
    @2
    cA
    cB
    elun
    vy
    vz
    cA
    cB
    @2
    shincl.1
    shincl.2
    shseli
    3imtr4i
    ssriv
end
