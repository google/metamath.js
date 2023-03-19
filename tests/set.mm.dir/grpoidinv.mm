include "cgr.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "wral.mm"
include "simpl.mm"
include "ralimi.mm"
include "oveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "rspccva.mm"
include "sylan.mm"
include "adantll.mm"
include "anim1i.mm"
include "adantrr.mm"
include "adantr.mm"
include "adantl.mm"
include "ad2antlr.mm"
include "simpr.mm"
include "jca32.mm"
include "biid.mm"
include "grpoidinvlem3.mm"
include "sylancom.mm"
include "grpoidinvlem4.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "jca31.mm"
include "ralrimiva.mm"
include "grpolidinv.mm"
include "reximddv.mm"

theorem grpoidinv
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cG: class G
  let cX: class X
  let vw: setvar w
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  assume grpfo.1: |- X = ran G

  disjoint x y
  disjoint u x
  disjoint u y
  disjoint G u
  disjoint G x
  disjoint G y
  disjoint X u
  disjoint X x
  disjoint X y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C z
  disjoint u w
  disjoint u z
  disjoint G w
  disjoint G z
  disjoint X w
  disjoint X z
  disjoint U y
  assert |- ( G e. GrpOp -> E. u e. X A. x e. X ( ( ( u G x ) = x /\ ( x G u ) = x ) /\ E. y e. X ( ( y G x ) = u /\ ( x G y ) = u ) ) )

  proof
    cG
    cgr
    wcel
    #
    vu
    cv
    #
    vz
    cv
    #
    cG
    co
    #
    @2
    wceq
    #
    vw
    cv
    @2
    cG
    co
    @1
    wceq
    vw
    cX
    wrex
    #
    wa
    #
    vz
    cX
    wral
    #
    @1
    vx
    cv
    #
    cG
    co
    #
    @8
    wceq
    #
    @8
    @1
    cG
    co
    #
    @8
    wceq
    #
    wa
    vy
    cv
    #
    @8
    cG
    co
    @1
    wceq
    @8
    @13
    cG
    co
    @1
    wceq
    wa
    vy
    cX
    wrex
    #
    wa
    #
    vx
    cX
    wral
    vu
    cX
    @0
    @1
    cX
    wcel
    #
    @7
    wa
    #
    wa
    #
    @15
    vx
    cX
    @18
    @8
    cX
    wcel
    #
    wa
    #
    @10
    @12
    @14
    @17
    @19
    @10
    @0
    @7
    @19
    @10
    @16
    @7
    @4
    vz
    cX
    wral
    #
    @19
    @10
    @6
    @4
    vz
    cX
    @4
    @5
    simpl
    ralimi
    #
    @4
    @10
    vz
    @8
    cX
    @2
    @8
    wceq
    #
    @3
    @9
    @2
    @8
    @2
    @8
    @1
    cG
    oveq2
    @23
    id
    eqeq12d
    rspccva
    sylan
    adantll
    adantll
    #
    @20
    @11
    @9
    @8
    @20
    @0
    @19
    wa
    @14
    @11
    @9
    wceq
    @18
    @0
    @19
    @0
    @17
    simpl
    anim1i
    @18
    @19
    @0
    @16
    wa
    #
    @21
    @5
    vz
    cX
    wral
    #
    wa
    wa
    @14
    @20
    @25
    @21
    @26
    @18
    @25
    @19
    @0
    @16
    @25
    @7
    @25
    id
    adantrr
    adantr
    @17
    @21
    @0
    @19
    @7
    @21
    @16
    @22
    adantl
    ad2antlr
    @17
    @26
    @0
    @19
    @7
    @26
    @16
    @6
    @5
    vz
    cX
    @4
    @5
    simpr
    ralimi
    adantl
    ad2antlr
    jca32
    @21
    @26
    vz
    vy
    vw
    @8
    @1
    cG
    cX
    grpfo.1
    @21
    biid
    @26
    biid
    grpoidinvlem3
    sylancom
    #
    vy
    @8
    @1
    cG
    cX
    grpfo.1
    grpoidinvlem4
    syl2anc
    @24
    eqtrd
    @27
    jca31
    ralrimiva
    vz
    vw
    vu
    cG
    cX
    grpfo.1
    grpolidinv
    reximddv
end
