include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cuni.mm"
include "wss.mm"
include "wa.mm"
include "com.mm"
include "cpw.mm"
include "wf.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wf1.mm"
include "wcel.mm"
include "wo.mm"
include "wn.mm"
include "wpss.mm"
include "vex.mm"
include "inf3lem5.mm"
include "dfpss2.mm"
include "simprbi.mm"
include "syl6.mm"
include "expdimp.mm"
include "adantrl.mm"
include "eqcom.mm"
include "sylnib.mm"
include "adantrr.mm"
include "jaod.mm"
include "con2d.mm"
include "wb.mm"
include "word.mm"
include "nnord.mm"
include "ordtri3.mm"
include "syl2an.mm"
include "adantl.mm"
include "sylibrd.mm"
include "ralrimivva.mm"
include "wfn.mm"
include "crn.mm"
include "crdg.mm"
include "cres.mm"
include "frfnom.mm"
include "fneq1.mm"
include "mpbiri.mm"
include "wrex.mm"
include "fvelrnb.mm"
include "inf3lemd.mm"
include "fvex.mm"
include "elpw.mm"
include "sylibr.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "rexlimiv.mm"
include "syl6bi.mm"
include "ssrdv.mm"
include "ancli.mm"
include "mp2b.mm"
include "df-f.mm"
include "mpbir.mm"
include "jctil.mm"
include "dff13.mm"

theorem inf3lem6
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f
  assume inf3lem.1: |- G = ( y e. _V |-> { w e. x | ( w i^i x ) C_ y } )
  assume inf3lem.2: |- F = ( rec ( G , (/) ) |` _om )
  assume inf3lem.3: |- A e. _V
  assume inf3lem.4: |- B e. _V

  disjoint x y
  disjoint w x
  disjoint w y
  disjoint v x
  disjoint u x
  disjoint f x
  disjoint v y
  disjoint u y
  disjoint f y
  disjoint v w
  disjoint u w
  disjoint f w
  disjoint u v
  disjoint f v
  disjoint f u
  disjoint G v
  disjoint G u
  disjoint G f
  disjoint F v
  disjoint F u
  disjoint F f
  disjoint A v
  disjoint A u
  disjoint A f
  disjoint B v
  disjoint B u
  disjoint B f
  assert |- ( ( x =/= (/) /\ x C_ U. x ) -> F : _om -1-1-> ~P x )

  proof
    vx
    cv
    #
    c0
    wne
    @0
    @0
    cuni
    wss
    wa
    #
    com
    @0
    cpw
    #
    cF
    wf
    #
    vv
    cv
    #
    cF
    cfv
    #
    vu
    cv
    #
    cF
    cfv
    #
    wceq
    #
    @4
    @6
    wceq
    #
    wi
    #
    vu
    com
    wral
    vv
    com
    wral
    #
    wa
    com
    @2
    cF
    wf1
    @1
    @11
    @3
    @1
    @10
    vv
    vu
    com
    com
    @1
    @4
    com
    wcel
    #
    @6
    com
    wcel
    #
    wa
    #
    wa
    #
    @8
    @4
    @6
    wcel
    #
    @6
    @4
    wcel
    #
    wo
    #
    wn
    #
    @9
    @15
    @18
    @8
    @15
    @16
    @8
    wn
    #
    @17
    @1
    @13
    @16
    @20
    wi
    @12
    @1
    @13
    @16
    @20
    @1
    @13
    @16
    wa
    @5
    @7
    wpss
    #
    @20
    vx
    vy
    vw
    @6
    @4
    cF
    cG
    inf3lem.1
    inf3lem.2
    vu
    vex
    #
    vv
    vex
    #
    inf3lem5
    @21
    @5
    @7
    wss
    @20
    @5
    @7
    dfpss2
    simprbi
    syl6
    expdimp
    adantrl
    @1
    @12
    @17
    @20
    wi
    @13
    @1
    @12
    @17
    @20
    @1
    @12
    @17
    wa
    @7
    @5
    wpss
    #
    @20
    vx
    vy
    vw
    @4
    @6
    cF
    cG
    inf3lem.1
    inf3lem.2
    @23
    @22
    inf3lem5
    @24
    @7
    @5
    wceq
    #
    @8
    @24
    @7
    @5
    wss
    @25
    wn
    @7
    @5
    dfpss2
    simprbi
    @7
    @5
    eqcom
    sylnib
    syl6
    expdimp
    adantrr
    jaod
    con2d
    @14
    @9
    @19
    wb
    #
    @1
    @12
    @4
    word
    @6
    word
    @26
    @13
    @4
    nnord
    @6
    nnord
    @4
    @6
    ordtri3
    syl2an
    adantl
    sylibrd
    ralrimivva
    @3
    cF
    com
    wfn
    #
    cF
    crn
    #
    @2
    wss
    #
    wa
    #
    cF
    cG
    c0
    crdg
    com
    cres
    #
    wceq
    #
    @27
    @30
    inf3lem.2
    @32
    @27
    @31
    com
    wfn
    c0
    cG
    frfnom
    com
    cF
    @31
    fneq1
    mpbiri
    @27
    @29
    @27
    vu
    @28
    @2
    @27
    @6
    @28
    wcel
    @5
    @6
    wceq
    #
    vv
    com
    wrex
    @6
    @2
    wcel
    #
    vv
    com
    @6
    cF
    fvelrnb
    @33
    @34
    vv
    com
    @12
    @5
    @2
    wcel
    #
    @33
    @34
    @12
    @5
    @0
    wss
    @35
    vx
    vy
    vw
    @4
    cB
    cF
    cG
    inf3lem.1
    inf3lem.2
    @23
    inf3lem.4
    inf3lemd
    @5
    @0
    @4
    cF
    fvex
    elpw
    sylibr
    @5
    @6
    @2
    eleq1
    syl5ibcom
    rexlimiv
    syl6bi
    ssrdv
    ancli
    mp2b
    com
    @2
    cF
    df-f
    mpbir
    jctil
    vv
    vu
    com
    @2
    cF
    dff13
    sylibr
end
