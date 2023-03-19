include "cph.mm"
include "co.mm"
include "chj.mm"
include "cv.mm"
include "wcel.mm"
include "cva.mm"
include "wceq.mm"
include "wrex.mm"
include "shseli.mm"
include "wa.mm"
include "wi.mm"
include "cun.mm"
include "ssun1.mm"
include "shunssji.mm"
include "sstri.mm"
include "sseli.mm"
include "ssun2.mm"
include "csh.mm"
include "cch.mm"
include "shjcl.mm"
include "mp2an.mm"
include "chshii.mm"
include "shaddcl.mm"
include "mp3an1.mm"
include "syl2an.mm"
include "eleq1a.mm"
include "syl.mm"
include "rexlimivv.mm"
include "sylbi.mm"
include "ssriv.mm"

theorem shsleji
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


  assert |- ( A +H B ) C_ ( A vH B )

  proof
    vx
    cA
    cB
    cph
    co
    #
    cA
    cB
    chj
    co
    #
    vx
    cv
    #
    @0
    wcel
    @2
    vy
    cv
    #
    vz
    cv
    #
    cva
    co
    #
    wceq
    #
    vz
    cB
    wrex
    vy
    cA
    wrex
    @2
    @1
    wcel
    #
    vy
    vz
    cA
    cB
    @2
    shincl.1
    shincl.2
    shseli
    @6
    @7
    vy
    vz
    cA
    cB
    @3
    cA
    wcel
    #
    @4
    cB
    wcel
    #
    wa
    @5
    @1
    wcel
    #
    @6
    @7
    wi
    @8
    @3
    @1
    wcel
    #
    @4
    @1
    wcel
    #
    @10
    @9
    cA
    @1
    @3
    cA
    cA
    cB
    cun
    #
    @1
    cA
    cB
    ssun1
    cA
    cB
    shincl.1
    shincl.2
    shunssji
    #
    sstri
    sseli
    cB
    @1
    @4
    cB
    @13
    @1
    cB
    cA
    ssun2
    @14
    sstri
    sseli
    @1
    csh
    wcel
    @11
    @12
    @10
    @1
    cA
    csh
    wcel
    cB
    csh
    wcel
    @1
    cch
    wcel
    shincl.1
    shincl.2
    cA
    cB
    shjcl
    mp2an
    chshii
    @3
    @4
    @1
    shaddcl
    mp3an1
    syl2an
    @5
    @1
    @2
    eleq1a
    syl
    rexlimivv
    sylbi
    ssriv
end
