include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "ccn.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "ccnp.mm"
include "wral.mm"
include "cflf.mm"
include "cflim.mm"
include "cfil.mm"
include "cncnp.mm"
include "wi.mm"
include "wb.mm"
include "cnpflf.mm"
include "3expa.mm"
include "adantlr.mm"
include "simplr.mm"
include "biantrurd.mm"
include "bitr4d.mm"
include "ralbidva.mm"
include "cuni.mm"
include "eqid.mm"
include "flimelbas.mm"
include "wceq.mm"
include "toponuni.mm"
include "ad2antrr.mm"
include "eleq2d.mm"
include "syl5ibr.mm"
include "pm4.71rd.mm"
include "imbi1d.mm"
include "impexp.mm"
include "syl6bb.mm"
include "ralbidv2.mm"
include "ralbidv.mm"
include "ralcom.mm"
include "pm5.32da.mm"
include "bitrd.mm"

theorem cnflf
  let vx: setvar x
  let vf: setvar f
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vu: setvar u
  let vv: setvar v
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cL: class L

  disjoint f x
  disjoint X f
  disjoint X x
  disjoint Y f
  disjoint Y x
  disjoint F f
  disjoint F x
  disjoint J f
  disjoint J x
  disjoint K f
  disjoint K x
  disjoint f u
  disjoint f v
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint L u
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint X u
  disjoint X v
  disjoint X z
  disjoint Y u
  disjoint Y v
  disjoint Y z
  disjoint F u
  disjoint F v
  disjoint F y
  disjoint F z
  disjoint J u
  disjoint J v
  disjoint J y
  disjoint J z
  disjoint K u
  disjoint K v
  disjoint K y
  disjoint K z
  assert |- ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` Y ) ) -> ( F e. ( J Cn K ) <-> ( F : X --> Y /\ A. f e. ( Fil ` X ) A. x e. ( J fLim f ) ( F ` x ) e. ( ( K fLimf f ) ` F ) ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    wa
    #
    cF
    cJ
    cK
    ccn
    co
    wcel
    cX
    cY
    cF
    wf
    #
    cF
    vx
    cv
    #
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    vx
    cX
    wral
    #
    wa
    @3
    @4
    cF
    cfv
    cF
    cK
    vf
    cv
    #
    cflf
    co
    cfv
    wcel
    #
    vx
    cJ
    @7
    cflim
    co
    #
    wral
    #
    vf
    cX
    cfil
    cfv
    #
    wral
    #
    wa
    vx
    cF
    cJ
    cK
    cX
    cY
    cncnp
    @2
    @3
    @6
    @12
    @2
    @3
    wa
    #
    @6
    @4
    @9
    wcel
    #
    @8
    wi
    #
    vf
    @11
    wral
    #
    vx
    cX
    wral
    #
    @12
    @13
    @5
    @16
    vx
    cX
    @13
    @4
    cX
    wcel
    #
    wa
    #
    @5
    @3
    @16
    wa
    #
    @16
    @2
    @18
    @5
    @20
    wb
    #
    @3
    @0
    @1
    @18
    @21
    @4
    vf
    cF
    cJ
    cK
    cX
    cY
    cnpflf
    3expa
    adantlr
    @19
    @3
    @16
    @2
    @3
    @18
    simplr
    biantrurd
    bitr4d
    ralbidva
    @13
    @12
    @15
    vx
    cX
    wral
    #
    vf
    @11
    wral
    @17
    @13
    @10
    @22
    vf
    @11
    @13
    @8
    @15
    vx
    @9
    cX
    @13
    @15
    @18
    @14
    wa
    #
    @8
    wi
    @18
    @15
    wi
    @13
    @14
    @23
    @8
    @13
    @14
    @18
    @14
    @18
    @13
    @4
    cJ
    cuni
    #
    wcel
    @4
    @7
    cJ
    @24
    @24
    eqid
    flimelbas
    @13
    cX
    @24
    @4
    @0
    cX
    @24
    wceq
    @1
    @3
    cX
    cJ
    toponuni
    ad2antrr
    eleq2d
    syl5ibr
    pm4.71rd
    imbi1d
    @18
    @14
    @8
    impexp
    syl6bb
    ralbidv2
    ralbidv
    @15
    vf
    vx
    @11
    cX
    ralcom
    syl6bb
    bitr4d
    pm5.32da
    bitrd
end
