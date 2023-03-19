include "wcel.mm"
include "cvv.mm"
include "wa.mm"
include "cop.mm"
include "ctpos.mm"
include "wbr.mm"
include "wb.mm"
include "cdm.mm"
include "ccnv.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "cuni.mm"
include "brtpos2.mm"
include "adantr.mm"
include "wi.mm"
include "opex.mm"
include "breldmg.mm"
include "3expia.mm"
include "mpan.mm"
include "opelcnvg.mm"
include "adantl.mm"
include "sylibrd.mm"
include "elun1.mm"
include "syl6.mm"
include "pm4.71rd.mm"
include "opswap.mm"
include "breq1i.mm"
include "anbi2i.mm"
include "syl6bbr.mm"
include "bitr4d.mm"
include "ex.mm"
include "wn.mm"
include "brtpos0.mm"
include "opprc.mm"
include "breq1d.mm"
include "ancom.mm"
include "sylnbi.mm"
include "bibi12d.mm"
include "syl5ibrcom.mm"
include "pm2.61d.mm"

theorem brtpos
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z
  let cG: class G


  assert |- ( C e. V -> ( <. A , B >. tpos F C <-> <. B , A >. F C ) )

  proof
    cC
    cV
    wcel
    #
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    wa
    #
    cA
    cB
    cop
    #
    cC
    cF
    ctpos
    #
    wbr
    #
    cB
    cA
    cop
    #
    cC
    cF
    wbr
    #
    wb
    #
    @0
    @3
    @9
    @0
    @3
    wa
    #
    @6
    @4
    cF
    cdm
    #
    ccnv
    #
    c0
    csn
    #
    cun
    wcel
    #
    @4
    csn
    ccnv
    cuni
    #
    cC
    cF
    wbr
    #
    wa
    #
    @8
    @0
    @6
    @17
    wb
    @3
    @4
    cC
    cF
    cV
    brtpos2
    adantr
    @10
    @8
    @14
    @8
    wa
    @17
    @10
    @8
    @14
    @10
    @8
    @4
    @12
    wcel
    #
    @14
    @10
    @8
    @7
    @11
    wcel
    #
    @18
    @0
    @8
    @19
    wi
    #
    @3
    @7
    cvv
    wcel
    #
    @0
    @20
    cB
    cA
    opex
    @21
    @0
    @8
    @19
    @7
    cC
    cvv
    cV
    cF
    breldmg
    3expia
    mpan
    adantr
    @3
    @18
    @19
    wb
    @0
    cA
    cB
    cvv
    cvv
    @11
    opelcnvg
    adantl
    sylibrd
    @4
    @12
    @13
    elun1
    syl6
    pm4.71rd
    @16
    @8
    @14
    @15
    @7
    cC
    cF
    cA
    cB
    opswap
    breq1i
    anbi2i
    syl6bbr
    bitr4d
    ex
    @0
    @9
    @3
    wn
    #
    c0
    cC
    @5
    wbr
    #
    c0
    cC
    cF
    wbr
    #
    wb
    cC
    cF
    cV
    brtpos0
    @22
    @6
    @23
    @8
    @24
    @22
    @4
    c0
    cC
    @5
    cA
    cB
    opprc
    breq1d
    @3
    @2
    @1
    wa
    #
    @8
    @24
    wb
    @1
    @2
    ancom
    @25
    wn
    @7
    c0
    cC
    cF
    cB
    cA
    opprc
    breq1d
    sylnbi
    bibi12d
    syl5ibrcom
    pm2.61d
end
