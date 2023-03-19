include "cr.mm"
include "wcel.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "covol.mm"
include "cfv.mm"
include "wceq.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "c1.mm"
include "caddc.mm"
include "wa.mm"
include "cmnf.mm"
include "cc0.mm"
include "cle.mm"
include "wss.mm"
include "cxr.mm"
include "pnfxr.mm"
include "icossre.mm"
include "mpan2.mm"
include "adantr.mm"
include "ovolge0.mm"
include "syl.mm"
include "mnflt0.mm"
include "wi.mm"
include "ovolcl.mm"
include "mnfxr.mm"
include "0xr.mm"
include "xrltletr.mm"
include "mp3an12.mm"
include "mpani.mm"
include "mpd.mm"
include "simpr.mm"
include "wb.mm"
include "xrrebnd.mm"
include "mpbir2and.mm"
include "ltp1d.mm"
include "cicc.mm"
include "cmin.mm"
include "simpl.mm"
include "peano2re.mm"
include "readdcld.mm"
include "0red.mm"
include "lep1d.mm"
include "letrd.mm"
include "addge02d.mm"
include "mpbid.mm"
include "ovolicc.mm"
include "syl3anc.mm"
include "recnd.mm"
include "pncand.mm"
include "eqtrd.mm"
include "cv.mm"
include "w3a.mm"
include "elicc2.mm"
include "syl2anc.mm"
include "biimpa.mm"
include "simp1d.mm"
include "simp2d.mm"
include "elicopnf.mm"
include "ad2antrr.mm"
include "ex.mm"
include "ssrdv.mm"
include "ovolss.mm"
include "eqbrtrrd.mm"
include "lenltd.mm"
include "pm2.65da.mm"
include "nltpnft.mm"
include "mpbird.mm"

theorem ovolicopnf
  let cA: class A
  let vx: setvar x


  assert |- ( A e. RR -> ( vol* ` ( A [,) +oo ) ) = +oo )

  proof
    cA
    cr
    wcel
    #
    cA
    cpnf
    cico
    co
    #
    covol
    cfv
    #
    cpnf
    wceq
    #
    @2
    cpnf
    clt
    wbr
    #
    wn
    #
    @0
    @4
    @2
    @2
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @0
    @4
    wa
    #
    @2
    @8
    @2
    cr
    wcel
    #
    cmnf
    @2
    clt
    wbr
    #
    @4
    @8
    cc0
    @2
    cle
    wbr
    #
    @10
    @8
    @1
    cr
    wss
    #
    @11
    @0
    @12
    @4
    @0
    cpnf
    cxr
    wcel
    @12
    pnfxr
    cA
    cpnf
    icossre
    mpan2
    #
    adantr
    #
    @1
    ovolge0
    syl
    #
    @8
    cmnf
    cc0
    clt
    wbr
    #
    @11
    @10
    mnflt0
    @8
    @2
    cxr
    wcel
    #
    @16
    @11
    wa
    @10
    wi
    #
    @0
    @17
    @4
    @0
    @12
    @17
    @13
    @1
    ovolcl
    syl
    #
    adantr
    #
    cmnf
    cxr
    wcel
    cc0
    cxr
    wcel
    @17
    @18
    mnfxr
    0xr
    cmnf
    cc0
    @2
    xrltletr
    mp3an12
    syl
    mpani
    mpd
    @0
    @4
    simpr
    @8
    @17
    @9
    @10
    @4
    wa
    wb
    @20
    @2
    xrrebnd
    syl
    mpbir2and
    #
    ltp1d
    @8
    @6
    @2
    cle
    wbr
    @7
    wn
    @8
    cA
    @6
    cA
    caddc
    co
    #
    cicc
    co
    #
    covol
    cfv
    #
    @6
    @2
    cle
    @8
    @24
    @22
    cA
    cmin
    co
    #
    @6
    @8
    @0
    @22
    cr
    wcel
    #
    cA
    @22
    cle
    wbr
    #
    @24
    @25
    wceq
    @0
    @4
    simpl
    #
    @8
    @6
    cA
    @8
    @9
    @6
    cr
    wcel
    @21
    @2
    peano2re
    syl
    #
    @28
    readdcld
    #
    @8
    cc0
    @6
    cle
    wbr
    @27
    @8
    cc0
    @2
    @6
    @8
    0red
    @21
    @29
    @15
    @8
    @2
    @21
    lep1d
    letrd
    @8
    cA
    @6
    @28
    @29
    addge02d
    mpbid
    cA
    @22
    ovolicc
    syl3anc
    @8
    @6
    cA
    @8
    @6
    @29
    recnd
    @8
    cA
    @28
    recnd
    pncand
    eqtrd
    @8
    @23
    @1
    wss
    @12
    @24
    @2
    cle
    wbr
    @8
    vx
    @23
    @1
    @8
    vx
    cv
    #
    @23
    wcel
    #
    @31
    @1
    wcel
    #
    @8
    @32
    wa
    #
    @33
    @31
    cr
    wcel
    #
    cA
    @31
    cle
    wbr
    #
    @34
    @35
    @36
    @31
    @22
    cle
    wbr
    #
    @8
    @32
    @35
    @36
    @37
    w3a
    #
    @8
    @0
    @26
    @32
    @38
    wb
    @28
    @30
    cA
    @22
    @31
    elicc2
    syl2anc
    biimpa
    #
    simp1d
    @34
    @35
    @36
    @37
    @39
    simp2d
    @0
    @33
    @35
    @36
    wa
    wb
    @4
    @32
    cA
    @31
    elicopnf
    ad2antrr
    mpbir2and
    ex
    ssrdv
    @14
    @23
    @1
    ovolss
    syl2anc
    eqbrtrrd
    @8
    @6
    @2
    @29
    @21
    lenltd
    mpbid
    pm2.65da
    @0
    @17
    @3
    @5
    wb
    @19
    @2
    nltpnft
    syl
    mpbird
end
