include "crn.mm"
include "cuz.mm"
include "cfv.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "com.mm"
include "wrex.mm"
include "wfn.mm"
include "wb.mm"
include "cvv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmpt.mm"
include "crdg.mm"
include "cres.mm"
include "frfnom.mm"
include "fneq1i.mm"
include "mpbir.mm"
include "fvelrnb.mm"
include "ax-mp.mm"
include "om2uzuzi.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "rexlimiv.mm"
include "sylbi.mm"
include "c0.mm"
include "om2uz0i.mm"
include "peano1.mm"
include "fnfvelrn.mm"
include "mp2an.mm"
include "eqeltrri.mm"
include "wi.mm"
include "wa.mm"
include "csuc.mm"
include "om2uzsuci.mm"
include "oveq1.mm"
include "sylan9eq.mm"
include "peano2.mm"
include "sylancr.mm"
include "adantr.mm"
include "eqeltrrd.mm"
include "rexlimiva.mm"
include "a1i.mm"
include "uzind4i.mm"
include "impbii.mm"
include "eqriv.mm"

theorem om2uzrani
  let vx: setvar x
  let cC: class C
  let cG: class G
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vw: setvar w
  let cB: class B
  let vv: setvar v
  assume om2uz.1: |- C e. ZZ
  assume om2uz.2: |- G = ( rec ( ( x e. _V |-> ( x + 1 ) ) , C ) |` _om )

  disjoint C x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint w z
  disjoint B w
  disjoint B z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint C v
  disjoint w x
  disjoint w y
  disjoint C w
  disjoint x y
  disjoint x z
  disjoint C y
  disjoint C z
  disjoint G v
  disjoint G w
  disjoint G y
  disjoint G z
  assert |- ran G = ( ZZ>= ` C )

  proof
    vy
    cG
    crn
    #
    cC
    cuz
    cfv
    #
    vy
    cv
    #
    @0
    wcel
    #
    @2
    @1
    wcel
    #
    @3
    vz
    cv
    #
    cG
    cfv
    #
    @2
    wceq
    #
    vz
    com
    wrex
    #
    @4
    cG
    com
    wfn
    #
    @3
    @8
    wb
    @9
    vx
    cvv
    vx
    cv
    c1
    caddc
    co
    cmpt
    #
    cC
    crdg
    com
    cres
    #
    com
    wfn
    cC
    @10
    frfnom
    com
    cG
    @11
    om2uz.2
    fneq1i
    mpbir
    #
    vz
    com
    @2
    cG
    fvelrnb
    ax-mp
    #
    @7
    @4
    vz
    com
    @5
    com
    wcel
    #
    @6
    @1
    wcel
    @7
    @4
    vx
    @5
    cC
    cG
    om2uz.1
    om2uz.2
    om2uzuzi
    @6
    @2
    @1
    eleq1
    syl5ibcom
    rexlimiv
    sylbi
    @5
    @0
    wcel
    cC
    @0
    wcel
    @3
    @2
    c1
    caddc
    co
    #
    @0
    wcel
    #
    @3
    vz
    vy
    cC
    @2
    om2uz.1
    @5
    cC
    @0
    eleq1
    @5
    @2
    @0
    eleq1
    #
    @5
    @15
    @0
    eleq1
    @17
    c0
    cG
    cfv
    #
    cC
    @0
    vx
    cC
    cG
    om2uz.1
    om2uz.2
    om2uz0i
    @9
    c0
    com
    wcel
    @18
    @0
    wcel
    @12
    peano1
    com
    c0
    cG
    fnfvelrn
    mp2an
    eqeltrri
    @3
    @16
    wi
    @4
    @3
    @8
    @16
    @13
    @7
    @16
    vz
    com
    @14
    @7
    wa
    @5
    csuc
    #
    cG
    cfv
    #
    @15
    @0
    @14
    @7
    @20
    @6
    c1
    caddc
    co
    @15
    vx
    @5
    cC
    cG
    om2uz.1
    om2uz.2
    om2uzsuci
    @6
    @2
    c1
    caddc
    oveq1
    sylan9eq
    @14
    @20
    @0
    wcel
    #
    @7
    @14
    @9
    @19
    com
    wcel
    @21
    @12
    @5
    peano2
    com
    @19
    cG
    fnfvelrn
    sylancr
    adantr
    eqeltrrd
    rexlimiva
    sylbi
    a1i
    uzind4i
    impbii
    eqriv
end
