include "wcel.mm"
include "cuni.mm"
include "wceq.mm"
include "wa.mm"
include "cref.mm"
include "wbr.mm"
include "cv.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "simpr.mm"
include "unisngl.mm"
include "syl6eq.mm"
include "csn.mm"
include "simplr.mm"
include "simprr.mm"
include "snssd.mm"
include "eqsstrd.mm"
include "simp-4r.mm"
include "eleqtrrd.mm"
include "eluni2.mm"
include "sylib.mm"
include "reximddv.mm"
include "abeq2i.mm"
include "biimpi.mm"
include "adantl.mm"
include "r19.29a.mm"
include "ralrimiva.mm"
include "cvv.mm"
include "wb.mm"
include "cpw.mm"
include "pwexg.mm"
include "snelpwi.mm"
include "ad2antlr.mm"
include "eqeltrd.mm"
include "ssriv.mm"
include "a1i.mm"
include "ssexd.mm"
include "adantr.mm"
include "eqid.mm"
include "isref.mm"
include "syl.mm"
include "mpbir2and.mm"

theorem dissnref
  let vx: setvar x
  let vu: setvar u
  let cC: class C
  let cV: class V
  let cX: class X
  let cY: class Y
  let vy: setvar y
  let vz: setvar z
  assume dissnref.c: |- C = { u | E. x e. X u = { x } }

  disjoint C u
  disjoint C x
  disjoint u x
  disjoint V u
  disjoint V x
  disjoint X u
  disjoint X x
  disjoint Y u
  disjoint Y x
  disjoint C y
  disjoint C z
  disjoint u y
  disjoint u z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint V y
  disjoint V z
  disjoint X y
  disjoint X z
  disjoint Y y
  assert |- ( ( X e. V /\ U. Y = X ) -> C Ref Y )

  proof
    cX
    cV
    wcel
    #
    cY
    cuni
    #
    cX
    wceq
    #
    wa
    #
    cC
    cY
    cref
    wbr
    #
    @1
    cC
    cuni
    #
    wceq
    #
    vu
    cv
    #
    vy
    cv
    #
    wss
    #
    vy
    cY
    wrex
    #
    vu
    cC
    wral
    #
    @3
    @1
    cX
    @5
    @0
    @2
    simpr
    vx
    vu
    cC
    cX
    dissnref.c
    unisngl
    syl6eq
    @3
    @10
    vu
    cC
    @3
    @7
    cC
    wcel
    #
    wa
    #
    @7
    vx
    cv
    #
    csn
    #
    wceq
    #
    @10
    vx
    cX
    @13
    @14
    cX
    wcel
    #
    wa
    #
    @16
    wa
    #
    @14
    @8
    wcel
    #
    @9
    vy
    cY
    @19
    @8
    cY
    wcel
    #
    @20
    wa
    #
    wa
    #
    @7
    @15
    @8
    @18
    @16
    @22
    simplr
    @23
    @14
    @8
    @19
    @21
    @20
    simprr
    snssd
    eqsstrd
    @19
    @14
    @1
    wcel
    @20
    vy
    cY
    wrex
    @19
    @14
    cX
    @1
    @13
    @17
    @16
    simplr
    @0
    @2
    @12
    @17
    @16
    simp-4r
    eleqtrrd
    vy
    @14
    cY
    eluni2
    sylib
    reximddv
    @12
    @16
    vx
    cX
    wrex
    #
    @3
    @12
    @24
    @24
    vu
    cC
    dissnref.c
    abeq2i
    biimpi
    #
    adantl
    r19.29a
    ralrimiva
    @3
    cC
    cvv
    wcel
    #
    @4
    @6
    @11
    wa
    wb
    @0
    @26
    @2
    @0
    cC
    cX
    cpw
    #
    cvv
    cX
    cV
    pwexg
    cC
    @27
    wss
    @0
    vu
    cC
    @27
    @12
    @16
    @7
    @27
    wcel
    vx
    cX
    @12
    @17
    wa
    #
    @16
    wa
    @7
    @15
    @27
    @28
    @16
    simpr
    @17
    @15
    @27
    wcel
    @12
    @16
    @14
    cX
    snelpwi
    ad2antlr
    eqeltrd
    @25
    r19.29a
    ssriv
    a1i
    ssexd
    adantr
    vu
    vy
    cC
    cY
    cvv
    @5
    @1
    @5
    eqid
    @1
    eqid
    isref
    syl
    mpbir2and
end
