include "cdomn.mm"
include "wcel.mm"
include "cnzr.mm"
include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "c0g.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "cbs.mm"
include "wral.mm"
include "domnnzr.mm"
include "ply1nz.mm"
include "syl.mm"
include "wa.mm"
include "wn.mm"
include "wne.mm"
include "neanior.mm"
include "cdg1.mm"
include "cn0.mm"
include "caddc.mm"
include "crlreg.mm"
include "eqid.mm"
include "crg.mm"
include "domnring.mm"
include "ad2antrr.mm"
include "simplrl.mm"
include "simprl.mm"
include "cco1.mm"
include "simpll.mm"
include "deg1ldgdomn.mm"
include "syl3anc.mm"
include "simplrr.mm"
include "simprr.mm"
include "deg1mul2.mm"
include "deg1nn0cl.mm"
include "nn0addcld.mm"
include "eqeltrd.mm"
include "wb.mm"
include "ply1ring.mm"
include "ringcl.mm"
include "deg1nn0clb.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "ex.mm"
include "syl5bir.mm"
include "necon4bd.mm"
include "ralrimivva.mm"
include "isdomn.mm"
include "sylanbrc.mm"

theorem ply1domn
  let cP: class P
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  assume ply1domn.p: |- P = ( Poly1 ` R )


  assert |- ( R e. Domn -> P e. Domn )

  proof
    cR
    cdomn
    wcel
    #
    cP
    cnzr
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
    cP
    c0g
    cfv
    #
    wceq
    @2
    @6
    wceq
    @3
    @6
    wceq
    wo
    #
    wi
    #
    vy
    cP
    cbs
    cfv
    #
    wral
    vx
    @9
    wral
    cP
    cdomn
    wcel
    @0
    cR
    cnzr
    wcel
    @1
    cR
    domnnzr
    cP
    cR
    ply1domn.p
    ply1nz
    syl
    @0
    @8
    vx
    vy
    @9
    @9
    @0
    @2
    @9
    wcel
    #
    @3
    @9
    wcel
    #
    wa
    #
    wa
    #
    @7
    @5
    @6
    @7
    wn
    @2
    @6
    wne
    #
    @3
    @6
    wne
    #
    wa
    #
    @13
    @5
    @6
    wne
    #
    @2
    @6
    @3
    @6
    neanior
    @13
    @16
    @17
    @13
    @16
    wa
    #
    @17
    @5
    cR
    cdg1
    cfv
    #
    cfv
    #
    cn0
    wcel
    #
    @18
    @20
    @2
    @19
    cfv
    #
    @3
    @19
    cfv
    #
    caddc
    co
    cn0
    @18
    @9
    @19
    cP
    cR
    @4
    cR
    crlreg
    cfv
    #
    @2
    @3
    @6
    @19
    eqid
    #
    ply1domn.p
    @24
    eqid
    #
    @9
    eqid
    #
    @4
    eqid
    #
    @6
    eqid
    #
    @0
    cR
    crg
    wcel
    #
    @12
    @16
    cR
    domnring
    #
    ad2antrr
    #
    @0
    @10
    @11
    @16
    simplrl
    #
    @13
    @14
    @15
    simprl
    #
    @18
    @0
    @10
    @14
    @22
    @2
    cco1
    cfv
    #
    cfv
    @24
    wcel
    @0
    @12
    @16
    simpll
    @33
    @34
    @35
    @9
    @19
    cP
    cR
    @24
    @2
    @6
    @25
    ply1domn.p
    @29
    @27
    @26
    @35
    eqid
    deg1ldgdomn
    syl3anc
    @0
    @10
    @11
    @16
    simplrr
    #
    @13
    @14
    @15
    simprr
    #
    deg1mul2
    @18
    @22
    @23
    @18
    @30
    @10
    @14
    @22
    cn0
    wcel
    @32
    @33
    @34
    @9
    @19
    cP
    cR
    @2
    @6
    @25
    ply1domn.p
    @29
    @27
    deg1nn0cl
    syl3anc
    @18
    @30
    @11
    @15
    @23
    cn0
    wcel
    @32
    @36
    @37
    @9
    @19
    cP
    cR
    @3
    @6
    @25
    ply1domn.p
    @29
    @27
    deg1nn0cl
    syl3anc
    nn0addcld
    eqeltrd
    @18
    @30
    @5
    @9
    wcel
    #
    @17
    @21
    wb
    @32
    @18
    cP
    crg
    wcel
    #
    @10
    @11
    @38
    @0
    @39
    @12
    @16
    @0
    @30
    @39
    @31
    cP
    cR
    ply1domn.p
    ply1ring
    syl
    ad2antrr
    @33
    @36
    @9
    cP
    @4
    @2
    @3
    @27
    @28
    ringcl
    syl3anc
    @9
    @19
    cP
    cR
    @5
    @6
    @25
    ply1domn.p
    @29
    @27
    deg1nn0clb
    syl2anc
    mpbird
    ex
    syl5bir
    necon4bd
    ralrimivva
    vx
    vy
    @9
    cP
    @4
    @6
    @27
    @28
    @29
    isdomn
    sylanbrc
end
