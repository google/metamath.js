include "ccla.mm"
include "wcel.mm"
include "cvv.mm"
include "elex.mm"
include "wn.mm"
include "c0.mm"
include "club.mm"
include "cfv.mm"
include "noel.mm"
include "wss.mm"
include "ssid.mm"
include "base0.mm"
include "eqid.mm"
include "clatlubcl.mm"
include "mpan2.mm"
include "mto.mm"
include "codu.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "eleq1d.mm"
include "mtbiri.mm"
include "con4i.mm"
include "cpo.mm"
include "cdm.mm"
include "cbs.mm"
include "cpw.mm"
include "wceq.mm"
include "cglb.mm"
include "wa.mm"
include "oduposb.mm"
include "ancom.mm"
include "odulub.mm"
include "dmeqd.mm"
include "eqeq1d.mm"
include "oduglb.mm"
include "anbi12d.mm"
include "syl5bb.mm"
include "isclat.mm"
include "odubas.mm"
include "3bitr4g.mm"
include "pm5.21nii.mm"

theorem oduclatb
  let cD: class D
  let cO: class O
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cL: class L
  let cU: class U
  let cV: class V
  let c.or: class .\/
  let c.an: class ./\
  assume oduglb.d: |- D = ( ODual ` O )


  assert |- ( O e. CLat <-> D e. CLat )

  proof
    cO
    ccla
    wcel
    #
    cO
    cvv
    wcel
    #
    cD
    ccla
    wcel
    #
    cO
    ccla
    elex
    @1
    @2
    @1
    wn
    #
    @2
    c0
    ccla
    wcel
    #
    @4
    c0
    c0
    club
    cfv
    #
    cfv
    #
    c0
    wcel
    #
    @6
    noel
    @4
    c0
    c0
    wss
    @7
    c0
    ssid
    c0
    c0
    @5
    c0
    base0
    @5
    eqid
    clatlubcl
    mpan2
    mto
    @3
    cD
    c0
    ccla
    @3
    cD
    cO
    codu
    cfv
    c0
    oduglb.d
    cO
    codu
    fvprc
    syl5eq
    eleq1d
    mtbiri
    con4i
    @1
    cO
    cpo
    wcel
    #
    cO
    club
    cfv
    #
    cdm
    #
    cO
    cbs
    cfv
    #
    cpw
    #
    wceq
    #
    cO
    cglb
    cfv
    #
    cdm
    #
    @12
    wceq
    #
    wa
    #
    wa
    cD
    cpo
    wcel
    #
    cD
    club
    cfv
    #
    cdm
    #
    @12
    wceq
    #
    cD
    cglb
    cfv
    #
    cdm
    #
    @12
    wceq
    #
    wa
    #
    wa
    @0
    @2
    @1
    @8
    @18
    @17
    @25
    cD
    cO
    cvv
    oduglb.d
    oduposb
    @17
    @16
    @13
    wa
    @1
    @25
    @13
    @16
    ancom
    @1
    @16
    @21
    @13
    @24
    @1
    @15
    @20
    @12
    @1
    @14
    @19
    cD
    @14
    cO
    cvv
    oduglb.d
    @14
    eqid
    #
    odulub
    dmeqd
    eqeq1d
    @1
    @10
    @23
    @12
    @1
    @9
    @22
    cD
    @9
    cO
    cvv
    oduglb.d
    @9
    eqid
    #
    oduglb
    dmeqd
    eqeq1d
    anbi12d
    syl5bb
    anbi12d
    @11
    @9
    @14
    cO
    @11
    eqid
    #
    @27
    @26
    isclat
    @11
    @19
    @22
    cD
    @11
    cD
    cO
    oduglb.d
    @28
    odubas
    @19
    eqid
    @22
    eqid
    isclat
    3bitr4g
    pm5.21nii
end
