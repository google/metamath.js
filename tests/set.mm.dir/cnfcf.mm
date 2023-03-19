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
include "cfcf.mm"
include "cfcls.mm"
include "cfil.mm"
include "cncnp.mm"
include "wi.mm"
include "wb.mm"
include "cnpfcf.mm"
include "3expa.mm"
include "adantlr.mm"
include "simplr.mm"
include "biantrurd.mm"
include "bitr4d.mm"
include "ralbidva.mm"
include "cuni.mm"
include "eqid.mm"
include "fclselbas.mm"
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
include "syl6rbbr.mm"
include "bitrd.mm"
include "pm5.32da.mm"

theorem cnfcf
  let vx: setvar x
  let vf: setvar f
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vg: setvar g
  let vh: setvar h
  let cA: class A
  let cL: class L

  disjoint f x
  disjoint F f
  disjoint F x
  disjoint J f
  disjoint J x
  disjoint K f
  disjoint K x
  disjoint X f
  disjoint X x
  disjoint Y f
  disjoint Y x
  disjoint f g
  disjoint f h
  disjoint A f
  disjoint g h
  disjoint A g
  disjoint A h
  disjoint g x
  disjoint F g
  disjoint h x
  disjoint F h
  disjoint J g
  disjoint J h
  disjoint K g
  disjoint K h
  disjoint L f
  disjoint X g
  disjoint X h
  disjoint Y g
  disjoint Y h
  assert |- ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` Y ) ) -> ( F e. ( J Cn K ) <-> ( F : X --> Y /\ A. f e. ( Fil ` X ) A. x e. ( J fClus f ) ( F ` x ) e. ( ( K fClusf f ) ` F ) ) ) )

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
    cfcf
    co
    cfv
    wcel
    #
    vx
    cJ
    @7
    cfcls
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
    cnpfcf
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
    fclselbas
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
    vx
    vf
    cX
    @11
    ralcom
    syl6rbbr
    bitrd
    pm5.32da
    bitrd
end
