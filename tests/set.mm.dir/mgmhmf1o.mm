include "cmgmhm.mm"
include "co.mm"
include "wcel.mm"
include "wf1o.mm"
include "ccnv.mm"
include "wa.mm"
include "cmgm.mm"
include "wf.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "mgmhmrcl.mm"
include "ancomd.mm"
include "adantr.mm"
include "f1ocnv.mm"
include "adantl.mm"
include "f1of.mm"
include "syl.mm"
include "simpll.mm"
include "simprl.mm"
include "ffvelrnd.mm"
include "simprr.mm"
include "eqid.mm"
include "mgmhmlin.mm"
include "syl3anc.mm"
include "simplr.mm"
include "f1ocnvfv2.mm"
include "syl2anc.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "wi.mm"
include "simpld.mm"
include "mgmcl.mm"
include "f1ocnvfv.mm"
include "mpd.mm"
include "ralrimivva.mm"
include "jca.mm"
include "ismgmhm.mm"
include "sylanbrc.mm"
include "wfn.mm"
include "mgmhmf.mm"
include "ffn.mm"
include "dff1o4.mm"
include "impbida.mm"

theorem mgmhmf1o
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume mgmhmf1o.b: |- B = ( Base ` R )
  assume mgmhmf1o.c: |- C = ( Base ` S )


  assert |- ( F e. ( R MgmHom S ) -> ( F : B -1-1-onto-> C <-> `' F e. ( S MgmHom R ) ) )

  proof
    cF
    cR
    cS
    cmgmhm
    co
    wcel
    #
    cB
    cC
    cF
    wf1o
    #
    cF
    ccnv
    #
    cS
    cR
    cmgmhm
    co
    wcel
    #
    @0
    @1
    wa
    #
    cS
    cmgm
    wcel
    #
    cR
    cmgm
    wcel
    #
    wa
    #
    cC
    cB
    @2
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cS
    cplusg
    cfv
    #
    co
    #
    @2
    cfv
    @9
    @2
    cfv
    #
    @10
    @2
    cfv
    #
    cR
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vy
    cC
    wral
    vx
    cC
    wral
    #
    wa
    @3
    @0
    @7
    @1
    @0
    @6
    @5
    cR
    cS
    cF
    mgmhmrcl
    #
    ancomd
    adantr
    @4
    @8
    @18
    @4
    cC
    cB
    @2
    wf1o
    #
    @8
    @1
    @20
    @0
    cB
    cC
    cF
    f1ocnv
    adantl
    cC
    cB
    @2
    f1of
    syl
    #
    @4
    @17
    vx
    vy
    cC
    cC
    @4
    @9
    cC
    wcel
    #
    @10
    cC
    wcel
    #
    wa
    #
    wa
    #
    @16
    cF
    cfv
    #
    @12
    wceq
    #
    @17
    @25
    @26
    @13
    cF
    cfv
    #
    @14
    cF
    cfv
    #
    @11
    co
    #
    @12
    @25
    @0
    @13
    cB
    wcel
    #
    @14
    cB
    wcel
    #
    @26
    @30
    wceq
    @0
    @1
    @24
    simpll
    @25
    cC
    cB
    @9
    @2
    @4
    @8
    @24
    @21
    adantr
    #
    @4
    @22
    @23
    simprl
    #
    ffvelrnd
    #
    @25
    cC
    cB
    @10
    @2
    @33
    @4
    @22
    @23
    simprr
    #
    ffvelrnd
    #
    cB
    @15
    @11
    cR
    cS
    cF
    @13
    @14
    mgmhmf1o.b
    @15
    eqid
    #
    @11
    eqid
    #
    mgmhmlin
    syl3anc
    @25
    @28
    @9
    @29
    @10
    @11
    @25
    @1
    @22
    @28
    @9
    wceq
    @0
    @1
    @24
    simplr
    #
    @34
    cB
    cC
    @9
    cF
    f1ocnvfv2
    syl2anc
    @25
    @1
    @23
    @29
    @10
    wceq
    @40
    @36
    cB
    cC
    @10
    cF
    f1ocnvfv2
    syl2anc
    oveq12d
    eqtrd
    @25
    @1
    @16
    cB
    wcel
    #
    @27
    @17
    wi
    @40
    @25
    @6
    @31
    @32
    @41
    @4
    @6
    @24
    @0
    @6
    @1
    @0
    @6
    @5
    @19
    simpld
    adantr
    adantr
    @35
    @37
    cB
    cR
    @13
    @14
    @15
    mgmhmf1o.b
    @38
    mgmcl
    syl3anc
    cB
    cC
    @16
    @12
    cF
    f1ocnvfv
    syl2anc
    mpd
    ralrimivva
    jca
    vx
    vy
    cC
    cB
    @11
    @15
    cS
    cR
    @2
    mgmhmf1o.c
    mgmhmf1o.b
    @39
    @38
    ismgmhm
    sylanbrc
    @0
    @3
    wa
    #
    cF
    cB
    wfn
    #
    @2
    cC
    wfn
    #
    @1
    @42
    cB
    cC
    cF
    wf
    #
    @43
    @0
    @45
    @3
    cB
    cC
    cR
    cS
    cF
    mgmhmf1o.b
    mgmhmf1o.c
    mgmhmf
    adantr
    cB
    cC
    cF
    ffn
    syl
    @42
    @8
    @44
    @3
    @8
    @0
    cC
    cB
    cS
    cR
    @2
    mgmhmf1o.c
    mgmhmf1o.b
    mgmhmf
    adantl
    cC
    cB
    @2
    ffn
    syl
    cB
    cC
    cF
    dff1o4
    sylanbrc
    impbida
end
