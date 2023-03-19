include "crh.mm"
include "co.mm"
include "wcel.mm"
include "wf1o.mm"
include "ccnv.mm"
include "wa.mm"
include "crg.mm"
include "cghm.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmhm.mm"
include "rhmrcl2.mm"
include "rhmrcl1.mm"
include "jca.mm"
include "adantr.mm"
include "simpr.mm"
include "wb.mm"
include "rhmghm.mm"
include "ghmf1o.mm"
include "bicomd.mm"
include "syl.mm"
include "mpbird.mm"
include "cbs.mm"
include "eqidd.mm"
include "wceq.mm"
include "eqid.mm"
include "mgpbas.mm"
include "a1i.mm"
include "f1oeq123d.mm"
include "biimpa.mm"
include "rhmmhm.mm"
include "mhmf1o.mm"
include "isrhm.mm"
include "sylanbrc.mm"
include "wfn.mm"
include "wf.mm"
include "rhmf.mm"
include "ffn.mm"
include "adantl.mm"
include "dff1o4.mm"
include "impbida.mm"

theorem rhmf1o
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  assume rhmf1o.b: |- B = ( Base ` R )
  assume rhmf1o.c: |- C = ( Base ` S )


  assert |- ( F e. ( R RingHom S ) -> ( F : B -1-1-onto-> C <-> `' F e. ( S RingHom R ) ) )

  proof
    cF
    cR
    cS
    crh
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
    crh
    co
    wcel
    #
    @0
    @1
    wa
    #
    cS
    crg
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    @2
    cS
    cR
    cghm
    co
    wcel
    #
    @2
    cS
    cmgp
    cfv
    #
    cR
    cmgp
    cfv
    #
    cmhm
    co
    wcel
    #
    wa
    @3
    @0
    @7
    @1
    @0
    @5
    @6
    cR
    cS
    cF
    rhmrcl2
    cR
    cS
    cF
    rhmrcl1
    jca
    adantr
    @4
    @8
    @11
    @4
    @8
    @1
    @0
    @1
    simpr
    @4
    cF
    cR
    cS
    cghm
    co
    wcel
    #
    @8
    @1
    wb
    @0
    @12
    @1
    cR
    cS
    cF
    rhmghm
    adantr
    @12
    @1
    @8
    cR
    cS
    cF
    cB
    cC
    rhmf1o.b
    rhmf1o.c
    ghmf1o
    bicomd
    syl
    mpbird
    @4
    @11
    @10
    cbs
    cfv
    #
    @9
    cbs
    cfv
    #
    cF
    wf1o
    #
    @0
    @1
    @15
    @0
    cB
    @13
    cC
    @14
    cF
    cF
    @0
    cF
    eqidd
    cB
    @13
    wceq
    @0
    cB
    cR
    @10
    @10
    eqid
    #
    rhmf1o.b
    mgpbas
    a1i
    cC
    @14
    wceq
    @0
    cC
    cS
    @9
    @9
    eqid
    #
    rhmf1o.c
    mgpbas
    a1i
    f1oeq123d
    biimpa
    @4
    cF
    @10
    @9
    cmhm
    co
    wcel
    #
    @11
    @15
    wb
    @0
    @18
    @1
    cR
    cS
    cF
    @10
    @9
    @16
    @17
    rhmmhm
    adantr
    @18
    @15
    @11
    @13
    @14
    @10
    @9
    cF
    @13
    eqid
    @14
    eqid
    mhmf1o
    bicomd
    syl
    mpbird
    jca
    cS
    cR
    @2
    @9
    @10
    @17
    @16
    isrhm
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
    @19
    cB
    cC
    cF
    wf
    #
    @20
    @0
    @22
    @3
    cB
    cC
    cR
    cS
    cF
    rhmf1o.b
    rhmf1o.c
    rhmf
    adantr
    cB
    cC
    cF
    ffn
    syl
    @19
    cC
    cB
    @2
    wf
    #
    @21
    @3
    @23
    @0
    cC
    cB
    cS
    cR
    @2
    rhmf1o.c
    rhmf1o.b
    rhmf
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
