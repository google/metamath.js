include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "c2.mm"
include "cr.mm"
include "cfv.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "nvcl.mm"
include "2re.mm"
include "jctil.mm"
include "c1.mm"
include "cneg.mm"
include "cns.mm"
include "caddc.mm"
include "cpv.mm"
include "cn0v.mm"
include "wceq.mm"
include "eqid.mm"
include "nvz0.mm"
include "adantr.mm"
include "1pneg1e0.mm"
include "oveq1i.mm"
include "nv0.mm"
include "syl5req.mm"
include "cc.mm"
include "neg1cn.mm"
include "ax-1cn.mm"
include "nvdir.mm"
include "mp3anr1.mm"
include "mpanr1.mm"
include "nvsid.mm"
include "oveq1d.mm"
include "3eqtrd.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "nvscl.mm"
include "mp3an2.mm"
include "nvtri.mm"
include "mpd3an3.mm"
include "eqbrtrd.mm"
include "nvm1.mm"
include "oveq2d.mm"
include "recnd.mm"
include "2timesd.mm"
include "eqtr4d.mm"
include "breqtrd.mm"
include "2pos.mm"
include "prodge0.mm"
include "syl2anc.mm"

theorem nvge0
  let cA: class A
  let cU: class U
  let cN: class N
  let cX: class X
  assume nvge0.1: |- X = ( BaseSet ` U )
  assume nvge0.6: |- N = ( normCV ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X ) -> 0 <_ ( N ` A ) )

  proof
    cU
    cnv
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    c2
    cr
    wcel
    #
    cA
    cN
    cfv
    #
    cr
    wcel
    #
    wa
    cc0
    c2
    clt
    wbr
    #
    cc0
    c2
    @4
    cmul
    co
    #
    cle
    wbr
    #
    wa
    cc0
    @4
    cle
    wbr
    @2
    @5
    @3
    cA
    cU
    cN
    cX
    nvge0.1
    nvge0.6
    nvcl
    #
    2re
    jctil
    @2
    @8
    @6
    @2
    cc0
    @4
    c1
    cneg
    #
    cA
    cU
    cns
    cfv
    #
    co
    #
    cN
    cfv
    #
    caddc
    co
    #
    @7
    cle
    @2
    cc0
    cA
    @12
    cU
    cpv
    cfv
    #
    co
    #
    cN
    cfv
    #
    @14
    cle
    @2
    cU
    cn0v
    cfv
    #
    cN
    cfv
    #
    cc0
    @17
    @0
    @19
    cc0
    wceq
    @1
    cU
    cN
    @18
    @18
    eqid
    #
    nvge0.6
    nvz0
    adantr
    @2
    @18
    @16
    cN
    @2
    @18
    c1
    @10
    caddc
    co
    #
    cA
    @11
    co
    #
    c1
    cA
    @11
    co
    #
    @12
    @15
    co
    #
    @16
    @2
    @22
    cc0
    cA
    @11
    co
    @18
    @21
    cc0
    cA
    @11
    1pneg1e0
    oveq1i
    cA
    @11
    cU
    cX
    @18
    nvge0.1
    @11
    eqid
    #
    @20
    nv0
    syl5req
    @0
    @10
    cc
    wcel
    #
    @1
    @22
    @24
    wceq
    #
    neg1cn
    @0
    c1
    cc
    wcel
    @26
    @1
    @27
    ax-1cn
    c1
    @10
    cA
    @11
    cU
    @15
    cX
    nvge0.1
    @15
    eqid
    #
    @25
    nvdir
    mp3anr1
    mpanr1
    @2
    @23
    cA
    @12
    @15
    cA
    @11
    cU
    cX
    nvge0.1
    @25
    nvsid
    oveq1d
    3eqtrd
    fveq2d
    eqtr3d
    @0
    @1
    @12
    cX
    wcel
    #
    @17
    @14
    cle
    wbr
    @0
    @26
    @1
    @29
    neg1cn
    @10
    cA
    @11
    cU
    cX
    nvge0.1
    @25
    nvscl
    mp3an2
    cA
    @12
    cU
    @15
    cN
    cX
    nvge0.1
    @28
    nvge0.6
    nvtri
    mpd3an3
    eqbrtrd
    @2
    @14
    @4
    @4
    caddc
    co
    @7
    @2
    @13
    @4
    @4
    caddc
    cA
    @11
    cU
    cN
    cX
    nvge0.1
    @25
    nvge0.6
    nvm1
    oveq2d
    @2
    @4
    @2
    @4
    @9
    recnd
    2timesd
    eqtr4d
    breqtrd
    2pos
    jctil
    c2
    @4
    prodge0
    syl2anc
end
