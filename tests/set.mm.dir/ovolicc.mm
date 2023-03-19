include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cicc.mm"
include "co.mm"
include "covol.mm"
include "cfv.mm"
include "cmin.mm"
include "wceq.mm"
include "cn.mm"
include "cv.mm"
include "c1.mm"
include "cop.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "cbvmptv.mm"
include "ovolicc1.mm"
include "cioo.mm"
include "ccom.mm"
include "crn.mm"
include "cuni.mm"
include "wss.mm"
include "caddc.mm"
include "cabs.mm"
include "cseq.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "wa.mm"
include "cxp.mm"
include "cin.mm"
include "cmap.mm"
include "wrex.mm"
include "crab.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "cbvrabv.mm"
include "ovolicc2.mm"
include "wb.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "ovolcl.mm"
include "syl.mm"
include "resubcld.mm"
include "rexrd.mm"
include "xrletri3.mm"
include "mpbir2and.mm"

theorem ovolicc
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. RR /\ B e. RR /\ A <_ B ) -> ( vol* ` ( A [,] B ) ) = ( B - A ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    w3a
    #
    cA
    cB
    cicc
    co
    #
    covol
    cfv
    #
    cB
    cA
    cmin
    co
    #
    wceq
    #
    @5
    @6
    cle
    wbr
    #
    @6
    @5
    cle
    wbr
    #
    @3
    cA
    cB
    vn
    vm
    cn
    vm
    cv
    #
    c1
    wceq
    #
    cA
    cB
    cop
    #
    cc0
    cc0
    cop
    #
    cif
    #
    cmpt
    @0
    @1
    @2
    simp1
    #
    @0
    @1
    @2
    simp2
    #
    @0
    @1
    @2
    simp3
    #
    vm
    vn
    cn
    @14
    vn
    cv
    #
    c1
    wceq
    #
    @12
    @13
    cif
    @10
    @18
    wceq
    @11
    @19
    @12
    @13
    @10
    @18
    c1
    eqeq1
    ifbid
    cbvmptv
    ovolicc1
    @3
    vy
    cA
    cB
    vf
    @4
    cioo
    vf
    cv
    #
    ccom
    crn
    cuni
    wss
    #
    vz
    cv
    #
    caddc
    cabs
    cmin
    ccom
    @20
    ccom
    c1
    cseq
    crn
    cxr
    clt
    csup
    #
    wceq
    #
    wa
    #
    vf
    cle
    cr
    cr
    cxp
    cin
    cn
    cmap
    co
    #
    wrex
    #
    vz
    cxr
    crab
    @15
    @16
    @17
    @27
    @21
    vy
    cv
    #
    @23
    wceq
    #
    wa
    #
    vf
    @26
    wrex
    vz
    vy
    cxr
    @22
    @28
    wceq
    #
    @25
    @30
    vf
    @26
    @31
    @24
    @29
    @21
    @22
    @28
    @23
    eqeq1
    anbi2d
    rexbidv
    cbvrabv
    ovolicc2
    @3
    @5
    cxr
    wcel
    #
    @6
    cxr
    wcel
    @7
    @8
    @9
    wa
    wb
    @3
    @4
    cr
    wss
    #
    @32
    @3
    @0
    @1
    @33
    @15
    @16
    cA
    cB
    iccssre
    syl2anc
    @4
    ovolcl
    syl
    @3
    @6
    @3
    cB
    cA
    @16
    @15
    resubcld
    rexrd
    @5
    @6
    xrletri3
    syl2anc
    mpbir2and
end
