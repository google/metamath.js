include "cphl.mm"
include "wcel.mm"
include "cpw.mm"
include "cv.mm"
include "wi.mm"
include "wss.mm"
include "cssss.mm"
include "selpw.mm"
include "sylibr.mm"
include "a1i.mm"
include "ssrdv.mm"
include "css1.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cint.mm"
include "cocv.mm"
include "cfv.mm"
include "wa.mm"
include "wal.mm"
include "intss1.mm"
include "eqid.mm"
include "ocv2ss.mm"
include "3syl.mm"
include "ad2antll.mm"
include "simprl.mm"
include "sseldd.mm"
include "wceq.mm"
include "simpl2.mm"
include "simprr.mm"
include "cssi.mm"
include "syl.mm"
include "eleqtrrd.mm"
include "expr.mm"
include "alrimiv.mm"
include "vex.mm"
include "elint.mm"
include "ex.mm"
include "wb.mm"
include "simp1.mm"
include "cuni.mm"
include "intssuni.mm"
include "3ad2ant3.mm"
include "simp2.mm"
include "3ad2ant1.mm"
include "sstrd.mm"
include "sspwuni.mm"
include "sylib.mm"
include "iscss2.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "ismred.mm"

theorem cssmre
  let cC: class C
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume cssmre.v: |- V = ( Base ` W )
  assume cssmre.c: |- C = ( CSubSp ` W )


  assert |- ( W e. PreHil -> C e. ( Moore ` V ) )

  proof
    cW
    cphl
    wcel
    #
    cC
    cV
    vx
    @0
    vx
    cC
    cV
    cpw
    #
    vx
    cv
    #
    cC
    wcel
    #
    @2
    @1
    wcel
    #
    wi
    @0
    @3
    @2
    cV
    wss
    @4
    cC
    @2
    cV
    cW
    cssmre.v
    cssmre.c
    cssss
    vx
    cV
    selpw
    sylibr
    a1i
    ssrdv
    #
    cC
    cV
    cW
    cssmre.v
    cssmre.c
    css1
    @0
    @2
    cC
    wss
    #
    @2
    c0
    wne
    #
    w3a
    #
    @2
    cint
    #
    cC
    wcel
    #
    @9
    cW
    cocv
    cfv
    #
    cfv
    #
    @11
    cfv
    #
    @9
    wss
    #
    @8
    vy
    @13
    @9
    @8
    vy
    cv
    #
    @13
    wcel
    #
    @15
    @9
    wcel
    #
    @8
    @16
    wa
    #
    vz
    cv
    #
    @2
    wcel
    #
    @15
    @19
    wcel
    #
    wi
    #
    vz
    wal
    @17
    @18
    @22
    vz
    @8
    @16
    @20
    @21
    @8
    @16
    @20
    wa
    #
    wa
    #
    @15
    @19
    @11
    cfv
    #
    @11
    cfv
    #
    @19
    @24
    @13
    @26
    @15
    @20
    @13
    @26
    wss
    #
    @8
    @16
    @20
    @9
    @19
    wss
    @25
    @12
    wss
    @27
    @19
    @2
    intss1
    @19
    @9
    @11
    cW
    @11
    eqid
    #
    ocv2ss
    @12
    @25
    @11
    cW
    @28
    ocv2ss
    3syl
    ad2antll
    @8
    @16
    @20
    simprl
    sseldd
    @24
    @19
    cC
    wcel
    @19
    @26
    wceq
    @24
    @2
    cC
    @19
    @0
    @6
    @7
    @23
    simpl2
    @8
    @16
    @20
    simprr
    sseldd
    cC
    @19
    @11
    cW
    @28
    cssmre.c
    cssi
    syl
    eleqtrrd
    expr
    alrimiv
    vz
    @15
    @2
    vy
    vex
    elint
    sylibr
    ex
    ssrdv
    @8
    @0
    @9
    cV
    wss
    @10
    @14
    wb
    @0
    @6
    @7
    simp1
    @8
    @9
    @2
    cuni
    #
    cV
    @7
    @0
    @9
    @29
    wss
    @6
    @2
    intssuni
    3ad2ant3
    @8
    @2
    @1
    wss
    @29
    cV
    wss
    @8
    @2
    cC
    @1
    @0
    @6
    @7
    simp2
    @0
    @6
    cC
    @1
    wss
    @7
    @5
    3ad2ant1
    sstrd
    @2
    cV
    sspwuni
    sylib
    sstrd
    cC
    @9
    @11
    cV
    cW
    cssmre.v
    cssmre.c
    @28
    iscss2
    syl2anc
    mpbird
    ismred
end
