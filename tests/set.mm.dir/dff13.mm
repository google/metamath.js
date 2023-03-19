include "wf1.mm"
include "wf.mm"
include "cv.mm"
include "wbr.mm"
include "wmo.mm"
include "wal.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "dff12.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "wcel.mm"
include "cdm.mm"
include "vex.mm"
include "breldm.mm"
include "fndm.mm"
include "eleq2d.mm"
include "syl5ib.mm"
include "anim12d.mm"
include "pm4.71rd.mm"
include "eqcom.mm"
include "fnbrfvb.mm"
include "syl5bb.mm"
include "bi2anan9.mm"
include "anandis.mm"
include "pm5.32da.mm"
include "bitr4d.mm"
include "imbi1d.mm"
include "impexp.mm"
include "syl6bb.mm"
include "albidv.mm"
include "19.21v.mm"
include "wex.mm"
include "19.23v.mm"
include "fvex.mm"
include "eqvinc.mm"
include "imbi1i.mm"
include "bitr4i.mm"
include "imbi2i.mm"
include "bitri.mm"
include "2albidv.mm"
include "breq1.mm"
include "mo4.mm"
include "albii.mm"
include "alrot3.mm"
include "r2al.mm"
include "3bitr4g.mm"
include "syl.mm"
include "pm5.32i.mm"

theorem dff13
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F x
  disjoint F y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint F z
  assert |- ( F : A -1-1-> B <-> ( F : A --> B /\ A. x e. A A. y e. A ( ( F ` x ) = ( F ` y ) -> x = y ) ) )

  proof
    cA
    cB
    cF
    wf1
    cA
    cB
    cF
    wf
    #
    vx
    cv
    #
    vz
    cv
    #
    cF
    wbr
    #
    vx
    wmo
    #
    vz
    wal
    #
    wa
    @0
    @1
    cF
    cfv
    #
    vy
    cv
    #
    cF
    cfv
    #
    wceq
    #
    @1
    @7
    wceq
    #
    wi
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    wa
    vx
    vz
    cA
    cB
    cF
    dff12
    @0
    @5
    @12
    @0
    cF
    cA
    wfn
    #
    @5
    @12
    wb
    cA
    cB
    cF
    ffn
    @13
    @3
    @7
    @2
    cF
    wbr
    #
    wa
    #
    @10
    wi
    #
    vz
    wal
    #
    vy
    wal
    vx
    wal
    #
    @1
    cA
    wcel
    #
    @7
    cA
    wcel
    #
    wa
    #
    @11
    wi
    #
    vy
    wal
    vx
    wal
    @5
    @12
    @13
    @17
    @22
    vx
    vy
    @13
    @17
    @21
    @2
    @6
    wceq
    #
    @2
    @8
    wceq
    #
    wa
    #
    @10
    wi
    #
    wi
    #
    vz
    wal
    #
    @22
    @13
    @16
    @27
    vz
    @13
    @16
    @21
    @25
    wa
    #
    @10
    wi
    @27
    @13
    @15
    @29
    @10
    @13
    @15
    @21
    @15
    wa
    @29
    @13
    @15
    @21
    @13
    @3
    @19
    @14
    @20
    @3
    @1
    cF
    cdm
    #
    wcel
    @13
    @19
    @1
    @2
    cF
    vx
    vex
    vz
    vex
    #
    breldm
    @13
    @30
    cA
    @1
    cA
    cF
    fndm
    #
    eleq2d
    syl5ib
    @14
    @7
    @30
    wcel
    @13
    @20
    @7
    @2
    cF
    vy
    vex
    @31
    breldm
    @13
    @30
    cA
    @7
    @32
    eleq2d
    syl5ib
    anim12d
    pm4.71rd
    @13
    @21
    @25
    @15
    @13
    @19
    @20
    @25
    @15
    wb
    @13
    @19
    wa
    #
    @23
    @3
    @13
    @20
    wa
    #
    @24
    @14
    @23
    @6
    @2
    wceq
    @33
    @3
    @2
    @6
    eqcom
    cA
    @1
    @2
    cF
    fnbrfvb
    syl5bb
    @24
    @8
    @2
    wceq
    @34
    @14
    @2
    @8
    eqcom
    cA
    @7
    @2
    cF
    fnbrfvb
    syl5bb
    bi2anan9
    anandis
    pm5.32da
    bitr4d
    imbi1d
    @21
    @25
    @10
    impexp
    syl6bb
    albidv
    @28
    @21
    @26
    vz
    wal
    #
    wi
    @22
    @21
    @26
    vz
    19.21v
    @35
    @11
    @21
    @35
    @25
    vz
    wex
    #
    @10
    wi
    @11
    @25
    @10
    vz
    19.23v
    @9
    @36
    @10
    vz
    @6
    @8
    @1
    cF
    fvex
    eqvinc
    imbi1i
    bitr4i
    imbi2i
    bitri
    syl6bb
    2albidv
    @5
    @16
    vy
    wal
    vx
    wal
    #
    vz
    wal
    @18
    @4
    @37
    vz
    @3
    @14
    vx
    vy
    @1
    @7
    @2
    cF
    breq1
    mo4
    albii
    @16
    vz
    vx
    vy
    alrot3
    bitri
    @11
    vx
    vy
    cA
    cA
    r2al
    3bitr4g
    syl
    pm5.32i
    bitri
end
