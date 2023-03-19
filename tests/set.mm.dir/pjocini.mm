include "cin.mm"
include "cort.mm"
include "cfv.mm"
include "wcel.mm"
include "cpjh.mm"
include "cmv.mm"
include "co.mm"
include "cch.mm"
include "chil.mm"
include "wceq.mm"
include "chincli.mm"
include "choccli.mm"
include "cheli.mm"
include "pjpo.mm"
include "sylancr.mm"
include "wss.mm"
include "inss1.mm"
include "chsscon3i.mm"
include "mpbi.mm"
include "pjcli.mm"
include "syl.mm"
include "sseldi.mm"
include "csh.mm"
include "chshii.mm"
include "shsubcl.mm"
include "mp3an1.mm"
include "mpdan.mm"
include "eqeltrd.mm"

theorem pjocini
  let cA: class A
  let cG: class G
  let cH: class H
  assume pjocin.1: |- G e. CH
  assume pjocin.2: |- H e. CH


  assert |- ( A e. ( _|_ ` ( G i^i H ) ) -> ( ( projh ` G ) ` A ) e. ( _|_ ` ( G i^i H ) ) )

  proof
    cA
    cG
    cH
    cin
    #
    cort
    cfv
    #
    wcel
    #
    cA
    cG
    cpjh
    cfv
    cfv
    #
    cA
    cA
    cG
    cort
    cfv
    #
    cpjh
    cfv
    cfv
    #
    cmv
    co
    #
    @1
    @2
    cG
    cch
    wcel
    cA
    chil
    wcel
    #
    @3
    @6
    wceq
    pjocin.1
    cA
    @1
    @0
    cG
    cH
    pjocin.1
    pjocin.2
    chincli
    #
    choccli
    #
    cheli
    #
    cA
    cG
    pjpo
    sylancr
    @2
    @5
    @1
    wcel
    #
    @6
    @1
    wcel
    #
    @2
    @4
    @1
    @5
    @0
    cG
    wss
    @4
    @1
    wss
    cG
    cH
    inss1
    @0
    cG
    @8
    pjocin.1
    chsscon3i
    mpbi
    @2
    @7
    @5
    @4
    wcel
    @10
    cA
    @4
    cG
    pjocin.1
    choccli
    pjcli
    syl
    sseldi
    @1
    csh
    wcel
    @2
    @11
    @12
    @1
    @9
    chshii
    cA
    @5
    @1
    shsubcl
    mp3an1
    mpdan
    eqeltrd
end
