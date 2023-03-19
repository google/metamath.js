include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cc0.mm"
include "csn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cv.mm"
include "cnmcv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "cba.mm"
include "wrex.mm"
include "cab.mm"
include "wf.mm"
include "eqid.mm"
include "0oo.mm"
include "nmooval.mm"
include "mpd3an3.mm"
include "df-sn.mm"
include "wb.mm"
include "cn0v.mm"
include "nvzcl.mm"
include "nvz0.mm"
include "0le1.mm"
include "syl6eqbr.mm"
include "fveq2.mm"
include "breq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "biantrurd.mm"
include "adantr.mm"
include "0oval.mm"
include "3expa.mm"
include "fveq2d.mm"
include "ad2antlr.mm"
include "eqtrd.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "rexbidva.mm"
include "r19.41v.mm"
include "syl6rbb.mm"
include "bitrd.mm"
include "abbidv.mm"
include "syl5req.mm"
include "supeq1d.mm"
include "wor.mm"
include "xrltso.mm"
include "0xr.mm"
include "supsn.mm"
include "mp2an.mm"
include "syl6eq.mm"

theorem nmoo0
  let cU: class U
  let cN: class N
  let cW: class W
  let cZ: class Z
  let vx: setvar x
  let vz: setvar z
  assume nmoo0.3: |- N = ( U normOpOLD W )
  assume nmoo0.0: |- Z = ( U 0op W )


  assert |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> ( N ` Z ) = 0 )

  proof
    cU
    cnv
    wcel
    #
    cW
    cnv
    wcel
    #
    wa
    #
    cZ
    cN
    cfv
    #
    cc0
    csn
    #
    cxr
    clt
    csup
    #
    cc0
    @2
    @3
    vz
    cv
    #
    cU
    cnmcv
    cfv
    #
    cfv
    #
    c1
    cle
    wbr
    #
    vx
    cv
    #
    @6
    cZ
    cfv
    #
    cW
    cnmcv
    cfv
    #
    cfv
    #
    wceq
    #
    wa
    #
    vz
    cU
    cba
    cfv
    #
    wrex
    #
    vx
    cab
    #
    cxr
    clt
    csup
    #
    @5
    @0
    @1
    @16
    cW
    cba
    cfv
    #
    cZ
    wf
    @3
    @19
    wceq
    cU
    cW
    @16
    @20
    cZ
    @16
    eqid
    #
    @20
    eqid
    #
    nmoo0.0
    0oo
    vx
    vz
    cZ
    cU
    @7
    @12
    cN
    cW
    @16
    @20
    @21
    @22
    @7
    eqid
    #
    @12
    eqid
    #
    nmoo0.3
    nmooval
    mpd3an3
    @2
    cxr
    @18
    @4
    clt
    @2
    @4
    @10
    cc0
    wceq
    #
    vx
    cab
    @18
    vx
    cc0
    df-sn
    @2
    @25
    @17
    vx
    @2
    @25
    @9
    vz
    @16
    wrex
    #
    @25
    wa
    #
    @17
    @0
    @25
    @27
    wb
    @1
    @0
    @26
    @25
    @0
    cU
    cn0v
    cfv
    #
    @16
    wcel
    @28
    @7
    cfv
    #
    c1
    cle
    wbr
    #
    @26
    cU
    @16
    @28
    @21
    @28
    eqid
    #
    nvzcl
    @0
    @29
    cc0
    c1
    cle
    cU
    @7
    @28
    @31
    @23
    nvz0
    0le1
    syl6eqbr
    @9
    @30
    vz
    @28
    @16
    @6
    @28
    wceq
    @8
    @29
    c1
    cle
    @6
    @28
    @7
    fveq2
    breq1d
    rspcev
    syl2anc
    biantrurd
    adantr
    @2
    @17
    @9
    @25
    wa
    #
    vz
    @16
    wrex
    @27
    @2
    @15
    @32
    vz
    @16
    @2
    @6
    @16
    wcel
    #
    wa
    #
    @14
    @25
    @9
    @34
    @13
    cc0
    @10
    @34
    @13
    cW
    cn0v
    cfv
    #
    @12
    cfv
    #
    cc0
    @34
    @11
    @35
    @12
    @0
    @1
    @33
    @11
    @35
    wceq
    @6
    cU
    cZ
    cW
    @16
    @35
    @21
    @35
    eqid
    #
    nmoo0.0
    0oval
    3expa
    fveq2d
    @1
    @36
    cc0
    wceq
    @0
    @33
    cW
    @12
    @35
    @37
    @24
    nvz0
    ad2antlr
    eqtrd
    eqeq2d
    anbi2d
    rexbidva
    @9
    @25
    vz
    @16
    r19.41v
    syl6rbb
    bitrd
    abbidv
    syl5req
    supeq1d
    eqtrd
    cxr
    clt
    wor
    cc0
    cxr
    wcel
    @5
    cc0
    wceq
    xrltso
    0xr
    cxr
    cc0
    clt
    supsn
    mp2an
    syl6eq
end
