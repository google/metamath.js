include "csh.mm"
include "wcel.mm"
include "wa.mm"
include "cph.mm"
include "co.mm"
include "cv.mm"
include "cva.mm"
include "wceq.mm"
include "wrex.mm"
include "cmv.mm"
include "shsel.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "id.mm"
include "chil.mm"
include "shel.mm"
include "hvaddsubval.mm"
include "syl2an.mm"
include "an4s.mm"
include "anassrs.mm"
include "sylan9eqr.mm"
include "cc.mm"
include "neg1cn.mm"
include "shmulcl.mm"
include "mp3an2.mm"
include "adantll.mm"
include "adantlr.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "sylan.mm"
include "syldan.mm"
include "ex.mm"
include "rexlimdva.mm"
include "hvsubval.mm"
include "impbid.mm"
include "rexbidva.mm"
include "bitrd.mm"

theorem shsel3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vz: setvar z
  let cD: class D

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint D x
  disjoint D y
  assert |- ( ( A e. SH /\ B e. SH ) -> ( C e. ( A +H B ) <-> E. x e. A E. y e. B C = ( x -h y ) ) )

  proof
    cA
    csh
    wcel
    #
    cB
    csh
    wcel
    #
    wa
    #
    cC
    cA
    cB
    cph
    co
    wcel
    cC
    vx
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
    #
    vx
    cA
    wrex
    cC
    @3
    vy
    cv
    #
    cmv
    co
    #
    wceq
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wrex
    vx
    vz
    cA
    cB
    cC
    shsel
    @2
    @7
    @11
    vx
    cA
    @2
    @3
    cA
    wcel
    #
    wa
    #
    @7
    @11
    @13
    @6
    @11
    vz
    cB
    @13
    @4
    cB
    wcel
    #
    wa
    #
    @6
    @11
    @15
    @6
    cC
    @3
    c1
    cneg
    #
    @4
    csm
    co
    #
    cmv
    co
    #
    wceq
    #
    @11
    @6
    @15
    cC
    @5
    @18
    @6
    id
    @2
    @12
    @14
    @5
    @18
    wceq
    #
    @0
    @12
    @1
    @14
    @20
    @0
    @12
    wa
    #
    @3
    chil
    wcel
    #
    @4
    chil
    wcel
    @20
    @1
    @14
    wa
    @3
    cA
    shel
    #
    @4
    cB
    shel
    @3
    @4
    hvaddsubval
    syl2an
    an4s
    anassrs
    sylan9eqr
    @15
    @17
    cB
    wcel
    #
    @19
    @11
    @2
    @14
    @24
    @12
    @1
    @14
    @24
    @0
    @1
    @16
    cc
    wcel
    #
    @14
    @24
    neg1cn
    @16
    @4
    cB
    shmulcl
    mp3an2
    adantll
    adantlr
    @10
    @19
    vy
    @17
    cB
    @8
    @17
    wceq
    @9
    @18
    cC
    @8
    @17
    @3
    cmv
    oveq2
    eqeq2d
    rspcev
    sylan
    syldan
    ex
    rexlimdva
    @13
    @10
    @7
    vy
    cB
    @13
    @8
    cB
    wcel
    #
    wa
    #
    @10
    @7
    @27
    @10
    cC
    @3
    @16
    @8
    csm
    co
    #
    cva
    co
    #
    wceq
    #
    @7
    @10
    @27
    cC
    @9
    @29
    @10
    id
    @2
    @12
    @26
    @9
    @29
    wceq
    #
    @0
    @12
    @1
    @26
    @31
    @21
    @22
    @8
    chil
    wcel
    @31
    @1
    @26
    wa
    @23
    @8
    cB
    shel
    @3
    @8
    hvsubval
    syl2an
    an4s
    anassrs
    sylan9eqr
    @27
    @28
    cB
    wcel
    #
    @30
    @7
    @2
    @26
    @32
    @12
    @1
    @26
    @32
    @0
    @1
    @25
    @26
    @32
    neg1cn
    @16
    @8
    cB
    shmulcl
    mp3an2
    adantll
    adantlr
    @6
    @30
    vz
    @28
    cB
    @4
    @28
    wceq
    @5
    @29
    cC
    @4
    @28
    @3
    cva
    oveq2
    eqeq2d
    rspcev
    sylan
    syldan
    ex
    rexlimdva
    impbid
    rexbidva
    bitrd
end
