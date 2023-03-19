include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "wne.mm"
include "cdm.mm"
include "crab.mm"
include "cres.mm"
include "cdif.mm"
include "cun.mm"
include "csupp.mm"
include "co.mm"
include "wss.mm"
include "wi.mm"
include "wn.mm"
include "eldif.mm"
include "wo.mm"
include "weq.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "neeq1d.mm"
include "elrab.mm"
include "ianor.mm"
include "xchnxbir.mm"
include "dmres.mm"
include "elin2.mm"
include "simpl.mm"
include "anim2i.mm"
include "ancomd.mm"
include "sylibr.mm"
include "ex.mm"
include "pm2.24.mm"
include "adantr.mm"
include "com12.mm"
include "jaoi.mm"
include "sylbi.mm"
include "adantl.mm"
include "wceq.mm"
include "snssi.mm"
include "resima2.mm"
include "syl.mm"
include "eqcomd.mm"
include "simpr.mm"
include "eqtrd.mm"
include "necon3d.mm"
include "impancom.mm"
include "con3d.mm"
include "impcom.mm"
include "eldifd.mm"
include "syl2anb.mm"
include "a1i.mm"
include "ssrdv.mm"
include "ssundif.mm"
include "suppval.mm"
include "cvv.mm"
include "resexg.mm"
include "sylan.mm"
include "uneq1d.mm"
include "3sstr4d.mm"

theorem ressuppssdif
  let cB: class B
  let cF: class F
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vx: setvar x
  let vz: setvar z


  assert |- ( ( F e. V /\ Z e. W ) -> ( F supp Z ) C_ ( ( ( F |` B ) supp Z ) u. ( dom F \ B ) ) )

  proof
    cF
    cV
    wcel
    #
    cZ
    cW
    wcel
    #
    wa
    #
    cF
    vz
    cv
    #
    csn
    #
    cima
    #
    cZ
    csn
    #
    wne
    #
    vz
    cF
    cdm
    #
    crab
    #
    cF
    cB
    cres
    #
    @4
    cima
    #
    @6
    wne
    #
    vz
    @10
    cdm
    #
    crab
    #
    @8
    cB
    cdif
    #
    cun
    #
    cF
    cZ
    csupp
    co
    @10
    cZ
    csupp
    co
    #
    @15
    cun
    @2
    @9
    @14
    cdif
    #
    @15
    wss
    @9
    @16
    wss
    @2
    vx
    @18
    @15
    vx
    cv
    #
    @18
    wcel
    #
    @19
    @15
    wcel
    #
    wi
    @2
    @20
    @19
    @9
    wcel
    #
    @19
    @14
    wcel
    #
    wn
    #
    wa
    @21
    @19
    @9
    @14
    eldif
    @22
    @19
    @8
    wcel
    #
    cF
    @19
    csn
    #
    cima
    #
    @6
    wne
    #
    wa
    #
    @19
    @13
    wcel
    #
    wn
    #
    @10
    @26
    cima
    #
    @6
    wne
    #
    wn
    #
    wo
    #
    @21
    @24
    @7
    @28
    vz
    @19
    @8
    vz
    vx
    weq
    #
    @5
    @27
    @6
    @36
    @4
    @26
    cF
    @3
    @19
    sneq
    #
    imaeq2d
    neeq1d
    elrab
    @30
    @33
    wa
    @35
    @23
    @30
    @33
    ianor
    @12
    @33
    vz
    @19
    @13
    @36
    @11
    @32
    @6
    @36
    @4
    @26
    @10
    @37
    imaeq2d
    neeq1d
    elrab
    xchnxbir
    @35
    @29
    @21
    @31
    @29
    @21
    wi
    #
    @34
    @31
    @19
    cB
    wcel
    #
    wn
    #
    @25
    wn
    #
    wo
    #
    @38
    @39
    @25
    wa
    @42
    @30
    @39
    @25
    ianor
    @19
    cB
    @8
    @13
    cF
    cB
    dmres
    elin2
    xchnxbir
    @40
    @38
    @41
    @40
    @29
    @21
    @40
    @29
    wa
    #
    @25
    @40
    wa
    @21
    @43
    @40
    @25
    @29
    @25
    @40
    @25
    @28
    simpl
    #
    anim2i
    ancomd
    @19
    @8
    cB
    eldif
    sylibr
    ex
    @29
    @41
    @21
    @25
    @41
    @21
    wi
    @28
    @25
    @21
    pm2.24
    adantr
    com12
    jaoi
    sylbi
    @34
    @29
    @21
    @34
    @29
    wa
    @19
    @8
    cB
    @29
    @25
    @34
    @44
    adantl
    @29
    @34
    @40
    @29
    @39
    @33
    @25
    @39
    @28
    @33
    @25
    @39
    wa
    #
    @32
    @6
    @27
    @6
    @45
    @32
    @6
    wceq
    #
    @27
    @6
    wceq
    @45
    @46
    wa
    @27
    @32
    @6
    @45
    @27
    @32
    wceq
    @46
    @45
    @32
    @27
    @45
    @26
    cB
    wss
    #
    @32
    @27
    wceq
    @39
    @47
    @25
    @19
    cB
    snssi
    adantl
    cF
    @26
    cB
    resima2
    syl
    eqcomd
    adantr
    @45
    @46
    simpr
    eqtrd
    ex
    necon3d
    impancom
    con3d
    impcom
    eldifd
    ex
    jaoi
    impcom
    syl2anb
    sylbi
    a1i
    ssrdv
    @9
    @14
    @15
    ssundif
    sylibr
    vz
    cV
    cW
    cF
    cZ
    suppval
    @2
    @17
    @14
    @15
    @0
    @10
    cvv
    wcel
    @1
    @17
    @14
    wceq
    cF
    cB
    cV
    resexg
    vz
    cvv
    cW
    @10
    cZ
    suppval
    sylan
    uneq1d
    3sstr4d
end
