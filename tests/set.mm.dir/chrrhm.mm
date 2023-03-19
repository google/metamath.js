include "crh.mm"
include "co.mm"
include "wcel.mm"
include "cchr.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "czrh.mm"
include "c0g.mm"
include "wceq.mm"
include "ccom.mm"
include "cz.mm"
include "wfn.mm"
include "zring.mm"
include "cbs.mm"
include "wf.mm"
include "crg.mm"
include "rhmrcl1.mm"
include "eqid.mm"
include "zrhrhm.mm"
include "syl.mm"
include "zringbas.mm"
include "rhmf.mm"
include "ffn.mm"
include "3syl.mm"
include "cn0.mm"
include "chrcl.mm"
include "nn0z.mm"
include "fvco2.mm"
include "syl2anc.mm"
include "chrid.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "rhmco.mm"
include "mpdan.mm"
include "wb.mm"
include "rhmrcl2.mm"
include "zrhrhmb.mm"
include "mpbid.mm"
include "fveq1d.mm"
include "cghm.mm"
include "rhmghm.mm"
include "ghmid.mm"
include "3eqtr3d.mm"
include "chrdvds.mm"
include "mpbird.mm"

theorem chrrhm
  let cR: class R
  let cS: class S
  let cF: class F


  assert |- ( F e. ( R RingHom S ) -> ( chr ` S ) || ( chr ` R ) )

  proof
    cF
    cR
    cS
    crh
    co
    wcel
    #
    cS
    cchr
    cfv
    #
    cR
    cchr
    cfv
    #
    cdvds
    wbr
    #
    @2
    cS
    czrh
    cfv
    #
    cfv
    #
    cS
    c0g
    cfv
    #
    wceq
    #
    @0
    @2
    cF
    cR
    czrh
    cfv
    #
    ccom
    #
    cfv
    #
    cR
    c0g
    cfv
    #
    cF
    cfv
    #
    @5
    @6
    @0
    @10
    @2
    @8
    cfv
    #
    cF
    cfv
    #
    @12
    @0
    @8
    cz
    wfn
    #
    @2
    cz
    wcel
    #
    @10
    @14
    wceq
    @0
    @8
    zring
    cR
    crh
    co
    wcel
    #
    cz
    cR
    cbs
    cfv
    #
    @8
    wf
    @15
    @0
    cR
    crg
    wcel
    #
    @17
    cR
    cS
    cF
    rhmrcl1
    #
    cR
    @8
    @8
    eqid
    #
    zrhrhm
    syl
    #
    cz
    @18
    zring
    cR
    @8
    zringbas
    @18
    eqid
    rhmf
    cz
    @18
    @8
    ffn
    3syl
    @0
    @19
    @2
    cn0
    wcel
    @16
    @20
    @2
    cR
    @2
    eqid
    #
    chrcl
    @2
    nn0z
    3syl
    #
    cz
    cF
    @8
    @2
    fvco2
    syl2anc
    @0
    @13
    @11
    cF
    @0
    @19
    @13
    @11
    wceq
    @20
    @2
    cR
    @8
    @11
    @23
    @21
    @11
    eqid
    #
    chrid
    syl
    fveq2d
    eqtrd
    @0
    @2
    @9
    @4
    @0
    @9
    zring
    cS
    crh
    co
    wcel
    #
    @9
    @4
    wceq
    #
    @0
    @17
    @26
    @22
    zring
    cR
    cS
    cF
    @8
    rhmco
    mpdan
    @0
    cS
    crg
    wcel
    #
    @26
    @27
    wb
    cR
    cS
    cF
    rhmrcl2
    #
    cS
    @9
    @4
    @4
    eqid
    #
    zrhrhmb
    syl
    mpbid
    fveq1d
    @0
    cF
    cR
    cS
    cghm
    co
    wcel
    @12
    @6
    wceq
    cR
    cS
    cF
    rhmghm
    cR
    cS
    cF
    @11
    @6
    @25
    @6
    eqid
    #
    ghmid
    syl
    3eqtr3d
    @0
    @28
    @16
    @3
    @7
    wb
    @29
    @24
    @1
    cS
    @4
    @2
    @6
    @1
    eqid
    @30
    @31
    chrdvds
    syl2anc
    mpbird
end
