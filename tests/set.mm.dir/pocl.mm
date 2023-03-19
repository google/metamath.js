include "wcel.mm"
include "w3a.mm"
include "wpo.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "cv.mm"
include "wceq.mm"
include "id.mm"
include "breq12d.mm"
include "notbid.mm"
include "breq1.mm"
include "anbi1d.mm"
include "imbi12d.mm"
include "anbi12d.mm"
include "imbi2d.mm"
include "breq2.mm"
include "imbi1d.mm"
include "anbi2d.mm"
include "wal.mm"
include "wral.mm"
include "df-po.mm"
include "r3al.mm"
include "sylbb.mm"
include "19.21bbi.mm"
include "19.21bi.mm"
include "com12.mm"
include "vtocl3ga.mm"

theorem pocl
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( R Po A -> ( ( B e. A /\ C e. A /\ D e. A ) -> ( -. B R B /\ ( ( B R C /\ C R D ) -> B R D ) ) ) )

  proof
    cB
    cA
    wcel
    cC
    cA
    wcel
    cD
    cA
    wcel
    w3a
    cA
    cR
    wpo
    #
    cB
    cB
    cR
    wbr
    #
    wn
    #
    cB
    cC
    cR
    wbr
    #
    cC
    cD
    cR
    wbr
    #
    wa
    #
    cB
    cD
    cR
    wbr
    #
    wi
    #
    wa
    #
    @0
    vx
    cv
    #
    @9
    cR
    wbr
    #
    wn
    #
    @9
    vy
    cv
    #
    cR
    wbr
    #
    @12
    vz
    cv
    #
    cR
    wbr
    #
    wa
    #
    @9
    @14
    cR
    wbr
    #
    wi
    #
    wa
    #
    wi
    @0
    @2
    cB
    @12
    cR
    wbr
    #
    @15
    wa
    #
    cB
    @14
    cR
    wbr
    #
    wi
    #
    wa
    #
    wi
    @0
    @2
    @3
    cC
    @14
    cR
    wbr
    #
    wa
    #
    @22
    wi
    #
    wa
    #
    wi
    @0
    @8
    wi
    vx
    vy
    vz
    cB
    cC
    cD
    cA
    cA
    cA
    @9
    cB
    wceq
    #
    @19
    @24
    @0
    @29
    @11
    @2
    @18
    @23
    @29
    @10
    @1
    @29
    @9
    cB
    @9
    cB
    cR
    @29
    id
    #
    @30
    breq12d
    notbid
    @29
    @16
    @21
    @17
    @22
    @29
    @13
    @20
    @15
    @9
    cB
    @12
    cR
    breq1
    anbi1d
    @9
    cB
    @14
    cR
    breq1
    imbi12d
    anbi12d
    imbi2d
    @12
    cC
    wceq
    #
    @24
    @28
    @0
    @31
    @23
    @27
    @2
    @31
    @21
    @26
    @22
    @31
    @20
    @3
    @15
    @25
    @12
    cC
    cB
    cR
    breq2
    @12
    cC
    @14
    cR
    breq1
    anbi12d
    imbi1d
    anbi2d
    imbi2d
    @14
    cD
    wceq
    #
    @28
    @8
    @0
    @32
    @27
    @7
    @2
    @32
    @26
    @5
    @22
    @6
    @32
    @25
    @4
    @3
    @14
    cD
    cC
    cR
    breq2
    anbi2d
    @14
    cD
    cB
    cR
    breq2
    imbi12d
    anbi2d
    imbi2d
    @0
    @9
    cA
    wcel
    @12
    cA
    wcel
    @14
    cA
    wcel
    w3a
    #
    @19
    @0
    @33
    @19
    wi
    #
    vz
    @0
    @34
    vz
    wal
    #
    vx
    vy
    @0
    @19
    vz
    cA
    wral
    vy
    cA
    wral
    vx
    cA
    wral
    @35
    vy
    wal
    vx
    wal
    vx
    vy
    vz
    cA
    cR
    df-po
    @19
    vx
    vy
    vz
    cA
    cA
    cA
    r3al
    sylbb
    19.21bbi
    19.21bi
    com12
    vtocl3ga
    com12
end
