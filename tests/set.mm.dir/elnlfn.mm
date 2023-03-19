include "chil.mm"
include "cc.mm"
include "wf.mm"
include "cnl.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "wceq.mm"
include "cdm.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "nlfnval.mm"
include "cnvimass.mm"
include "syl6eqss.mm"
include "fdm.mm"
include "sseqtrd.mm"
include "sseld.mm"
include "pm4.71rd.mm"
include "wb.mm"
include "eleq2d.mm"
include "adantr.mm"
include "wfn.mm"
include "ffn.mm"
include "cv.mm"
include "wi.mm"
include "eleq1.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "bibi12d.mm"
include "imbi2d.mm"
include "wbr.mm"
include "fnbrfvb.mm"
include "0cn.mm"
include "vex.mm"
include "eliniseg.mm"
include "ax-mp.mm"
include "syl6rbbr.mm"
include "expcom.mm"
include "vtoclga.mm"
include "mpan9.mm"
include "bitrd.mm"
include "pm5.32da.mm"

theorem elnlfn
  let cA: class A
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cS: class S


  assert |- ( T : ~H --> CC -> ( A e. ( null ` T ) <-> ( A e. ~H /\ ( T ` A ) = 0 ) ) )

  proof
    chil
    cc
    cT
    wf
    #
    cA
    cT
    cnl
    cfv
    #
    wcel
    #
    cA
    chil
    wcel
    #
    @2
    wa
    @3
    cA
    cT
    cfv
    #
    cc0
    wceq
    #
    wa
    @0
    @2
    @3
    @0
    @1
    chil
    cA
    @0
    @1
    cT
    cdm
    #
    chil
    @0
    @1
    cT
    ccnv
    cc0
    csn
    #
    cima
    #
    @6
    cT
    nlfnval
    #
    cT
    @7
    cnvimass
    syl6eqss
    chil
    cc
    cT
    fdm
    sseqtrd
    sseld
    pm4.71rd
    @0
    @3
    @2
    @5
    @0
    @3
    wa
    @2
    cA
    @8
    wcel
    #
    @5
    @0
    @2
    @10
    wb
    @3
    @0
    @1
    @8
    cA
    @9
    eleq2d
    adantr
    @0
    cT
    chil
    wfn
    #
    @3
    @10
    @5
    wb
    #
    chil
    cc
    cT
    ffn
    @11
    vx
    cv
    #
    @8
    wcel
    #
    @13
    cT
    cfv
    #
    cc0
    wceq
    #
    wb
    #
    wi
    @11
    @12
    wi
    vx
    cA
    chil
    @13
    cA
    wceq
    #
    @17
    @12
    @11
    @18
    @14
    @10
    @16
    @5
    @13
    cA
    @8
    eleq1
    @18
    @15
    @4
    cc0
    @13
    cA
    cT
    fveq2
    eqeq1d
    bibi12d
    imbi2d
    @11
    @13
    chil
    wcel
    #
    @17
    @11
    @19
    wa
    @16
    @13
    cc0
    cT
    wbr
    #
    @14
    chil
    @13
    cc0
    cT
    fnbrfvb
    cc0
    cc
    wcel
    @14
    @20
    wb
    0cn
    cT
    cc0
    @13
    cc
    vx
    vex
    eliniseg
    ax-mp
    syl6rbbr
    expcom
    vtoclga
    mpan9
    bitrd
    pm5.32da
    bitrd
end
