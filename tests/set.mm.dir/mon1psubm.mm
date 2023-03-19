include "cnzr.mm"
include "wcel.mm"
include "csubmnd.mm"
include "cfv.mm"
include "cbs.mm"
include "wss.mm"
include "cur.mm"
include "cv.mm"
include "cmulr.mm"
include "co.mm"
include "wral.mm"
include "eqid.mm"
include "mon1pcl.mm"
include "ssriv.mm"
include "a1i.mm"
include "cdg1.mm"
include "cc0.mm"
include "wceq.mm"
include "mon1pid.mm"
include "simpld.mm"
include "wa.mm"
include "c0g.mm"
include "wne.mm"
include "cco1.mm"
include "crg.mm"
include "ply1nz.mm"
include "nzrring.mm"
include "syl.mm"
include "adantr.mm"
include "ad2antrl.mm"
include "simprr.mm"
include "sseldi.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "cn0.mm"
include "caddc.mm"
include "crlreg.mm"
include "mon1pn0.mm"
include "mon1pldg.mm"
include "cui.mm"
include "unitrrg.mm"
include "1unit.mm"
include "sseldd.mm"
include "eqeltrd.mm"
include "ad2antll.mm"
include "deg1mul2.mm"
include "deg1nn0cl.mm"
include "nn0addcld.mm"
include "wb.mm"
include "deg1nn0clb.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "fveq2d.mm"
include "coe1mul4.mm"
include "oveq12d.mm"
include "ringidcl.mm"
include "ringlidm.mm"
include "eqtrd.mm"
include "ismon1p.mm"
include "syl3anbrc.mm"
include "ralrimivva.mm"
include "cmnd.mm"
include "w3a.mm"
include "ringmgp.mm"
include "mgpbas.mm"
include "ringidval.mm"
include "mgpplusg.mm"
include "issubm.mm"
include "mpbir3and.mm"

theorem mon1psubm
  let cP: class P
  let cR: class R
  let cU: class U
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  assume mon1psubm.p: |- P = ( Poly1 ` R )
  assume mon1psubm.m: |- M = ( Monic1p ` R )
  assume mon1psubm.u: |- U = ( mulGrp ` P )


  assert |- ( R e. NzRing -> M e. ( SubMnd ` U ) )

  proof
    cR
    cnzr
    wcel
    #
    cM
    cU
    csubmnd
    cfv
    wcel
    #
    cM
    cP
    cbs
    cfv
    #
    wss
    #
    cP
    cur
    cfv
    #
    cM
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cP
    cmulr
    cfv
    #
    co
    #
    cM
    wcel
    #
    vy
    cM
    wral
    vx
    cM
    wral
    #
    @3
    @0
    vx
    cM
    @2
    @2
    cP
    cR
    @6
    cM
    mon1psubm.p
    @2
    eqid
    #
    mon1psubm.m
    mon1pcl
    #
    ssriv
    #
    a1i
    @0
    @5
    @4
    cR
    cdg1
    cfv
    #
    cfv
    cc0
    wceq
    @15
    cP
    cR
    @4
    cM
    mon1psubm.p
    @4
    eqid
    #
    mon1psubm.m
    @15
    eqid
    #
    mon1pid
    simpld
    @0
    @10
    vx
    vy
    cM
    cM
    @0
    @6
    cM
    wcel
    #
    @7
    cM
    wcel
    #
    wa
    #
    wa
    #
    @9
    @2
    wcel
    #
    @9
    cP
    c0g
    cfv
    #
    wne
    #
    @9
    @15
    cfv
    #
    @9
    cco1
    cfv
    #
    cfv
    #
    cR
    cur
    cfv
    #
    wceq
    @10
    @21
    cP
    crg
    wcel
    #
    @6
    @2
    wcel
    #
    @7
    @2
    wcel
    #
    @22
    @0
    @29
    @20
    @0
    cP
    cnzr
    wcel
    @29
    cP
    cR
    mon1psubm.p
    ply1nz
    cP
    nzrring
    syl
    #
    adantr
    @18
    @30
    @0
    @19
    @13
    ad2antrl
    #
    @21
    cM
    @2
    @7
    @14
    @0
    @18
    @19
    simprr
    sseldi
    #
    @2
    cP
    @8
    @6
    @7
    @12
    @8
    eqid
    #
    ringcl
    syl3anc
    #
    @21
    @24
    @25
    cn0
    wcel
    #
    @21
    @25
    @6
    @15
    cfv
    #
    @7
    @15
    cfv
    #
    caddc
    co
    #
    cn0
    @21
    @2
    @15
    cP
    cR
    @8
    cR
    crlreg
    cfv
    #
    @6
    @7
    @23
    @17
    mon1psubm.p
    @41
    eqid
    #
    @12
    @35
    @23
    eqid
    #
    @0
    cR
    crg
    wcel
    #
    @20
    cR
    nzrring
    #
    adantr
    #
    @33
    @18
    @6
    @23
    wne
    #
    @0
    @19
    cP
    cR
    @6
    cM
    @23
    mon1psubm.p
    @43
    mon1psubm.m
    mon1pn0
    ad2antrl
    #
    @21
    @38
    @6
    cco1
    cfv
    cfv
    #
    @28
    @41
    @18
    @49
    @28
    wceq
    @0
    @19
    @15
    cR
    @28
    @6
    cM
    @17
    @28
    eqid
    #
    mon1psubm.m
    mon1pldg
    ad2antrl
    #
    @0
    @28
    @41
    wcel
    @20
    @0
    cR
    cui
    cfv
    #
    @41
    @28
    @0
    @44
    @52
    @41
    wss
    @45
    cR
    @52
    @41
    @42
    @52
    eqid
    #
    unitrrg
    syl
    @0
    @44
    @28
    @52
    wcel
    @45
    cR
    @52
    @28
    @53
    @50
    1unit
    syl
    sseldd
    adantr
    eqeltrd
    @34
    @19
    @7
    @23
    wne
    #
    @0
    @18
    cP
    cR
    @7
    cM
    @23
    mon1psubm.p
    @43
    mon1psubm.m
    mon1pn0
    ad2antll
    #
    deg1mul2
    #
    @21
    @38
    @39
    @21
    @44
    @30
    @47
    @38
    cn0
    wcel
    @46
    @33
    @48
    @2
    @15
    cP
    cR
    @6
    @23
    @17
    mon1psubm.p
    @43
    @12
    deg1nn0cl
    syl3anc
    @21
    @44
    @31
    @54
    @39
    cn0
    wcel
    @46
    @34
    @55
    @2
    @15
    cP
    cR
    @7
    @23
    @17
    mon1psubm.p
    @43
    @12
    deg1nn0cl
    syl3anc
    nn0addcld
    eqeltrd
    @21
    @44
    @22
    @24
    @37
    wb
    @46
    @36
    @2
    @15
    cP
    cR
    @9
    @23
    @17
    mon1psubm.p
    @43
    @12
    deg1nn0clb
    syl2anc
    mpbird
    @21
    @27
    @40
    @26
    cfv
    #
    @28
    @21
    @25
    @40
    @26
    @56
    fveq2d
    @21
    @57
    @49
    @39
    @7
    cco1
    cfv
    cfv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    @28
    @21
    @2
    @15
    cR
    @8
    @59
    @6
    @7
    cP
    @23
    mon1psubm.p
    @35
    @59
    eqid
    #
    @12
    @17
    @43
    @46
    @33
    @48
    @34
    @55
    coe1mul4
    @21
    @60
    @28
    @28
    @59
    co
    #
    @28
    @21
    @49
    @28
    @58
    @28
    @59
    @51
    @19
    @58
    @28
    wceq
    @0
    @18
    @15
    cR
    @28
    @7
    cM
    @17
    @50
    mon1psubm.m
    mon1pldg
    ad2antll
    oveq12d
    @0
    @62
    @28
    wceq
    #
    @20
    @0
    @44
    @28
    cR
    cbs
    cfv
    #
    wcel
    #
    @63
    @45
    @0
    @44
    @65
    @45
    @64
    cR
    @28
    @64
    eqid
    #
    @50
    ringidcl
    syl
    @64
    cR
    @59
    @28
    @28
    @66
    @61
    @50
    ringlidm
    syl2anc
    adantr
    eqtrd
    eqtrd
    eqtrd
    @2
    @15
    cP
    cR
    @28
    @9
    cM
    @23
    mon1psubm.p
    @12
    @43
    @17
    mon1psubm.m
    @50
    ismon1p
    syl3anbrc
    ralrimivva
    @0
    cU
    cmnd
    wcel
    #
    @1
    @3
    @5
    @11
    w3a
    wb
    @0
    @29
    @67
    @32
    cP
    cU
    mon1psubm.u
    ringmgp
    syl
    vx
    vy
    @2
    @8
    cM
    cU
    @4
    @2
    cP
    cU
    mon1psubm.u
    @12
    mgpbas
    cP
    @4
    cU
    mon1psubm.u
    @16
    ringidval
    cP
    @8
    cU
    mon1psubm.u
    @35
    mgpplusg
    issubm
    syl
    mpbir3and
end
