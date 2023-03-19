include "wcel.mm"
include "cort.mm"
include "cfv.mm"
include "cpjh.mm"
include "c0v.mm"
include "wceq.mm"
include "c0h.mm"
include "cin.mm"
include "wa.mm"
include "cmv.mm"
include "co.mm"
include "pjopi.mm"
include "csh.mm"
include "chshii.mm"
include "pjclii.mm"
include "shsubcl.mm"
include "mp3an13.mm"
include "syl5eqel.mm"
include "choccli.mm"
include "jctir.mm"
include "elin.mm"
include "sylibr.mm"
include "ocin.mm"
include "ax-mp.mm"
include "syl6eleq.mm"
include "elch0.mm"
include "sylib.mm"
include "cva.mm"
include "pjpji.mm"
include "oveq2.mm"
include "syl5eq.mm"
include "chil.mm"
include "pjhclii.mm"
include "ax-hvaddid.mm"
include "syl6eq.mm"
include "syl6eqel.mm"
include "impbii.mm"

theorem pjoc1i
  let cA: class A
  let cH: class H
  assume pjop.1: |- H e. CH
  assume pjop.2: |- A e. ~H


  assert |- ( A e. H <-> ( ( projh ` ( _|_ ` H ) ) ` A ) = 0h )

  proof
    cA
    cH
    wcel
    #
    cA
    cH
    cort
    cfv
    #
    cpjh
    cfv
    cfv
    #
    c0v
    wceq
    #
    @0
    @2
    c0h
    wcel
    @3
    @0
    @2
    cH
    @1
    cin
    #
    c0h
    @0
    @2
    cH
    wcel
    #
    @2
    @1
    wcel
    #
    wa
    @2
    @4
    wcel
    @0
    @5
    @6
    @0
    @2
    cA
    cA
    cH
    cpjh
    cfv
    cfv
    #
    cmv
    co
    #
    cH
    cA
    cH
    pjop.1
    pjop.2
    pjopi
    cH
    csh
    wcel
    #
    @0
    @7
    cH
    wcel
    @8
    cH
    wcel
    cH
    pjop.1
    chshii
    #
    cA
    cH
    pjop.1
    pjop.2
    pjclii
    #
    cA
    @7
    cH
    shsubcl
    mp3an13
    syl5eqel
    cA
    @1
    cH
    pjop.1
    choccli
    pjop.2
    pjclii
    jctir
    @2
    cH
    @1
    elin
    sylibr
    @9
    @4
    c0h
    wceq
    @10
    cH
    ocin
    ax-mp
    syl6eleq
    @2
    elch0
    sylib
    @3
    cA
    @7
    cH
    @3
    cA
    @7
    c0v
    cva
    co
    #
    @7
    @3
    cA
    @7
    @2
    cva
    co
    @12
    cA
    cH
    pjop.1
    pjop.2
    pjpji
    @2
    c0v
    @7
    cva
    oveq2
    syl5eq
    @7
    chil
    wcel
    @12
    @7
    wceq
    cA
    cH
    pjop.1
    pjop.2
    pjhclii
    @7
    ax-hvaddid
    ax-mp
    syl6eq
    @11
    syl6eqel
    impbii
end
