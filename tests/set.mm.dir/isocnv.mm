include "wf1o.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wb.mm"
include "wral.mm"
include "wa.mm"
include "ccnv.mm"
include "wiso.mm"
include "f1ocnv.mm"
include "adantr.mm"
include "wcel.mm"
include "wceq.mm"
include "f1ocnvfv2.mm"
include "adantrr.mm"
include "adantrl.mm"
include "breq12d.mm"
include "adantlr.mm"
include "wf.mm"
include "f1of.mm"
include "syl.mm"
include "ffvelrn.mm"
include "anim12dan.mm"
include "breq1.mm"
include "fveq2.mm"
include "breq1d.mm"
include "bibi12d.mm"
include "bicom.mm"
include "syl6bb.mm"
include "breq2d.mm"
include "breq2.mm"
include "rspc2va.mm"
include "sylan.mm"
include "an32s.mm"
include "sylanl1.mm"
include "bitr3d.mm"
include "ralrimivva.mm"
include "jca.mm"
include "df-isom.mm"
include "3imtr4i.mm"

theorem isocnv
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cH: class H
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D


  assert |- ( H Isom R , S ( A , B ) -> `' H Isom S , R ( B , A ) )

  proof
    cA
    cB
    cH
    wf1o
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    @1
    cH
    cfv
    #
    @2
    cH
    cfv
    #
    cS
    wbr
    #
    wb
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    wa
    #
    cB
    cA
    cH
    ccnv
    #
    wf1o
    #
    vz
    cv
    #
    vw
    cv
    #
    cS
    wbr
    #
    @12
    @10
    cfv
    #
    @13
    @10
    cfv
    #
    cR
    wbr
    #
    wb
    #
    vw
    cB
    wral
    vz
    cB
    wral
    #
    wa
    cA
    cB
    cR
    cS
    cH
    wiso
    cB
    cA
    cS
    cR
    @10
    wiso
    @9
    @11
    @19
    @0
    @11
    @8
    cA
    cB
    cH
    f1ocnv
    #
    adantr
    @9
    @18
    vz
    vw
    cB
    cB
    @9
    @12
    cB
    wcel
    #
    @13
    cB
    wcel
    #
    wa
    #
    wa
    @15
    cH
    cfv
    #
    @16
    cH
    cfv
    #
    cS
    wbr
    #
    @14
    @17
    @0
    @23
    @26
    @14
    wb
    @8
    @0
    @23
    wa
    @24
    @12
    @25
    @13
    cS
    @0
    @21
    @24
    @12
    wceq
    @22
    cA
    cB
    @12
    cH
    f1ocnvfv2
    adantrr
    @0
    @22
    @25
    @13
    wceq
    @21
    cA
    cB
    @13
    cH
    f1ocnvfv2
    adantrl
    breq12d
    adantlr
    @0
    cB
    cA
    @10
    wf
    #
    @8
    @23
    @26
    @17
    wb
    #
    @0
    @11
    @27
    @20
    cB
    cA
    @10
    f1of
    syl
    @27
    @23
    @8
    @28
    @27
    @23
    wa
    @15
    cA
    wcel
    #
    @16
    cA
    wcel
    #
    wa
    @8
    @28
    @27
    @21
    @29
    @22
    @30
    cB
    cA
    @12
    @10
    ffvelrn
    cB
    cA
    @13
    @10
    ffvelrn
    anim12dan
    @7
    @28
    @24
    @5
    cS
    wbr
    #
    @15
    @2
    cR
    wbr
    #
    wb
    #
    vx
    vy
    @15
    @16
    cA
    cA
    @1
    @15
    wceq
    #
    @7
    @32
    @31
    wb
    @33
    @34
    @3
    @32
    @6
    @31
    @1
    @15
    @2
    cR
    breq1
    @34
    @4
    @24
    @5
    cS
    @1
    @15
    cH
    fveq2
    breq1d
    bibi12d
    @32
    @31
    bicom
    syl6bb
    @2
    @16
    wceq
    #
    @31
    @26
    @32
    @17
    @35
    @5
    @25
    @24
    cS
    @2
    @16
    cH
    fveq2
    breq2d
    @2
    @16
    @15
    cR
    breq2
    bibi12d
    rspc2va
    sylan
    an32s
    sylanl1
    bitr3d
    ralrimivva
    jca
    vx
    vy
    cA
    cB
    cR
    cS
    cH
    df-isom
    vz
    vw
    cB
    cA
    cS
    cR
    @10
    df-isom
    3imtr4i
end
