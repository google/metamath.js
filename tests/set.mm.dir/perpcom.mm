include "cperpg.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "cs3.mm"
include "crag.mm"
include "wcel.mm"
include "wral.mm"
include "cin.mm"
include "wrex.mm"
include "wceq.mm"
include "incom.mm"
include "a1i.mm"
include "wa.mm"
include "ralcom.mm"
include "cmir.mm"
include "eqid.mm"
include "cstrkg.mm"
include "ad3antrrr.mm"
include "crn.mm"
include "simplrr.mm"
include "tglnpt.mm"
include "inss1.mm"
include "simpllr.mm"
include "sseldi.mm"
include "simplrl.mm"
include "simpr.mm"
include "ragcom.mm"
include "impbida.mm"
include "2ralbidva.mm"
include "syl5bb.mm"
include "rexeqbidva.mm"
include "isperp.mm"
include "3bitr4d.mm"
include "mpbid.mm"

theorem perpcom
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let va: setvar a
  let vb: setvar b
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vg: setvar g
  assume isperp.p: |- P = ( Base ` G )
  assume isperp.d: |- .- = ( dist ` G )
  assume isperp.i: |- I = ( Itv ` G )
  assume isperp.l: |- L = ( LineG ` G )
  assume isperp.g: |- ( ph -> G e. TarskiG )
  assume isperp.a: |- ( ph -> A e. ran L )
  assume isperp.b: |- ( ph -> B e. ran L )
  assume perpcom.1: |- ( ph -> A ( perpG ` G ) B )


  assert |- ( ph -> B ( perpG ` G ) A )

  proof
    wph
    cA
    cB
    cG
    cperpg
    cfv
    #
    wbr
    #
    cB
    cA
    @0
    wbr
    #
    perpcom.1
    wph
    vu
    cv
    #
    vx
    cv
    #
    vv
    cv
    #
    cs3
    cG
    crag
    cfv
    #
    wcel
    #
    vv
    cB
    wral
    vu
    cA
    wral
    #
    vx
    cA
    cB
    cin
    #
    wrex
    @5
    @4
    @3
    cs3
    @6
    wcel
    #
    vu
    cA
    wral
    vv
    cB
    wral
    #
    vx
    cB
    cA
    cin
    #
    wrex
    @1
    @2
    wph
    @8
    @11
    vx
    @9
    @12
    @9
    @12
    wceq
    wph
    cA
    cB
    incom
    a1i
    @8
    @7
    vu
    cA
    wral
    vv
    cB
    wral
    wph
    @4
    @9
    wcel
    #
    wa
    #
    @11
    @7
    vu
    vv
    cA
    cB
    ralcom
    @14
    @7
    @10
    vv
    vu
    cB
    cA
    @14
    @5
    cB
    wcel
    #
    @3
    cA
    wcel
    #
    wa
    #
    wa
    #
    @7
    @10
    @18
    @7
    wa
    #
    @3
    @4
    @5
    cP
    cG
    cmir
    cfv
    #
    cG
    cI
    cL
    c.mi
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    @20
    eqid
    #
    wph
    cG
    cstrkg
    wcel
    #
    @13
    @17
    @7
    isperp.g
    ad3antrrr
    #
    @19
    cA
    cP
    cG
    cI
    cL
    @3
    isperp.p
    isperp.l
    isperp.i
    @23
    wph
    cA
    cL
    crn
    #
    wcel
    #
    @13
    @17
    @7
    isperp.a
    ad3antrrr
    #
    @14
    @15
    @16
    @7
    simplrr
    tglnpt
    @19
    cA
    cP
    cG
    cI
    cL
    @4
    isperp.p
    isperp.l
    isperp.i
    @23
    @26
    @19
    @9
    cA
    @4
    cA
    cB
    inss1
    #
    wph
    @13
    @17
    @7
    simpllr
    sseldi
    tglnpt
    @19
    cB
    cP
    cG
    cI
    cL
    @5
    isperp.p
    isperp.l
    isperp.i
    @23
    wph
    cB
    @24
    wcel
    #
    @13
    @17
    @7
    isperp.b
    ad3antrrr
    @14
    @15
    @16
    @7
    simplrl
    tglnpt
    @18
    @7
    simpr
    ragcom
    @18
    @10
    wa
    #
    @5
    @4
    @3
    cP
    @20
    cG
    cI
    cL
    c.mi
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    @21
    wph
    @22
    @13
    @17
    @10
    isperp.g
    ad3antrrr
    #
    @29
    cB
    cP
    cG
    cI
    cL
    @5
    isperp.p
    isperp.l
    isperp.i
    @30
    wph
    @28
    @13
    @17
    @10
    isperp.b
    ad3antrrr
    @14
    @15
    @16
    @10
    simplrl
    tglnpt
    @29
    cA
    cP
    cG
    cI
    cL
    @4
    isperp.p
    isperp.l
    isperp.i
    @30
    wph
    @25
    @13
    @17
    @10
    isperp.a
    ad3antrrr
    #
    @29
    @9
    cA
    @4
    @27
    wph
    @13
    @17
    @10
    simpllr
    sseldi
    tglnpt
    @29
    cA
    cP
    cG
    cI
    cL
    @3
    isperp.p
    isperp.l
    isperp.i
    @30
    @31
    @14
    @15
    @16
    @10
    simplrr
    tglnpt
    @18
    @10
    simpr
    ragcom
    impbida
    2ralbidva
    syl5bb
    rexeqbidva
    wph
    vx
    vv
    vu
    cA
    cB
    cP
    cG
    cI
    cL
    c.mi
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    isperp.g
    isperp.a
    isperp.b
    isperp
    wph
    vx
    vu
    vv
    cB
    cA
    cP
    cG
    cI
    cL
    c.mi
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    isperp.g
    isperp.b
    isperp.a
    isperp
    3bitr4d
    mpbid
end
