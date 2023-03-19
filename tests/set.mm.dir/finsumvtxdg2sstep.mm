include "cupgr.mm"
include "wcel.mm"
include "wa.mm"
include "cfn.mm"
include "cv.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "csu.mm"
include "c2.mm"
include "chash.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cres.mm"
include "finresfin.mm"
include "ad2antll.mm"
include "syl5eqel.mm"
include "csn.mm"
include "cdif.mm"
include "caddc.mm"
include "cdm.mm"
include "crab.mm"
include "cun.mm"
include "csb.mm"
include "difsnid.mm"
include "ad2antlr.mm"
include "eqcomd.mm"
include "sumeq1d.mm"
include "wnel.mm"
include "cz.mm"
include "wral.mm"
include "diffi.mm"
include "adantr.mm"
include "adantl.mm"
include "simpr.mm"
include "neldifsn.mm"
include "nelir.mm"
include "a1i.mm"
include "cn0.mm"
include "dmfi.mm"
include "wi.mm"
include "eleq2d.mm"
include "biimpd.mm"
include "imp.mm"
include "eqid.mm"
include "vtxdgfisnn0.mm"
include "syl2an2r.mm"
include "nn0zd.mm"
include "ralrimiva.mm"
include "fsumsplitsnun.mm"
include "syl121anc.mm"
include "fveq2.mm"
include "csbied.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "cbvrabv.mm"
include "finsumvtxdg2ssteplem2.mm"
include "finsumvtxdg2ssteplem4.mm"
include "fveq2i.mm"
include "oveq2i.mm"
include "finsumvtxdg2ssteplem1.mm"
include "ex.mm"
include "embantd.mm"

theorem finsumvtxdg2sstep
  let vv: setvar v
  let cP: class P
  let cS: class S
  let vi: setvar i
  let cE: class E
  let cG: class G
  let cI: class I
  let cK: class K
  let cN: class N
  let cV: class V
  let vj: setvar j
  assume finsumvtxdg2sstep.v: |- V = ( Vtx ` G )
  assume finsumvtxdg2sstep.e: |- E = ( iEdg ` G )
  assume finsumvtxdg2sstep.k: |- K = ( V \ { N } )
  assume finsumvtxdg2sstep.i: |- I = { i e. dom E | N e/ ( E ` i ) }
  assume finsumvtxdg2sstep.p: |- P = ( E |` I )
  assume finsumvtxdg2sstep.s: |- S = <. K , P >.

  disjoint E i
  disjoint G i
  disjoint N i
  disjoint E v
  disjoint G v
  disjoint K v
  disjoint N v
  disjoint V i
  disjoint V v
  disjoint i v
  disjoint E j
  disjoint i j
  disjoint N j
  assert |- ( ( ( G e. UPGraph /\ N e. V ) /\ ( V e. Fin /\ E e. Fin ) ) -> ( ( P e. Fin -> sum_ v e. K ( ( VtxDeg ` S ) ` v ) = ( 2 x. ( # ` P ) ) ) -> sum_ v e. V ( ( VtxDeg ` G ) ` v ) = ( 2 x. ( # ` E ) ) ) )

  proof
    cG
    cupgr
    wcel
    #
    cN
    cV
    wcel
    #
    wa
    #
    cV
    cfn
    wcel
    #
    cE
    cfn
    wcel
    #
    wa
    #
    wa
    #
    cP
    cfn
    wcel
    cK
    vv
    cv
    #
    cS
    cvtxdg
    cfv
    cfv
    vv
    csu
    c2
    cP
    chash
    cfv
    #
    cmul
    co
    wceq
    #
    cV
    @7
    cG
    cvtxdg
    cfv
    #
    cfv
    #
    vv
    csu
    #
    c2
    cE
    chash
    cfv
    #
    cmul
    co
    #
    wceq
    #
    @6
    cP
    cE
    cI
    cres
    #
    cfn
    finsumvtxdg2sstep.p
    @4
    @16
    cfn
    wcel
    @2
    @3
    cI
    cE
    finresfin
    ad2antll
    syl5eqel
    @6
    @9
    @15
    @6
    @9
    wa
    #
    @12
    cV
    cN
    csn
    #
    cdif
    #
    @11
    vv
    csu
    #
    cN
    @10
    cfv
    #
    caddc
    co
    #
    c2
    @8
    cN
    vi
    cv
    #
    cE
    cfv
    #
    wcel
    #
    vi
    cE
    cdm
    #
    crab
    #
    chash
    cfv
    #
    caddc
    co
    #
    cmul
    co
    #
    @14
    @6
    @12
    @22
    wceq
    @9
    @6
    @12
    @19
    @18
    cun
    #
    @11
    vv
    csu
    #
    @20
    vv
    cN
    @11
    csb
    #
    caddc
    co
    #
    @22
    @6
    cV
    @31
    @11
    vv
    @6
    @31
    cV
    @1
    @31
    cV
    wceq
    @0
    @5
    cV
    cN
    difsnid
    #
    ad2antlr
    eqcomd
    sumeq1d
    @6
    @19
    cfn
    wcel
    #
    @1
    cN
    @19
    wnel
    #
    @11
    cz
    wcel
    #
    vv
    @31
    wral
    @32
    @34
    wceq
    @5
    @36
    @2
    @3
    @36
    @4
    cV
    @18
    diffi
    adantr
    adantl
    @2
    @1
    @5
    @0
    @1
    simpr
    #
    adantr
    @37
    @6
    cN
    @19
    cN
    cV
    neldifsn
    nelir
    a1i
    @6
    @38
    vv
    @31
    @6
    @7
    @31
    wcel
    #
    wa
    @11
    @6
    @26
    cfn
    wcel
    #
    @40
    @7
    cV
    wcel
    #
    @11
    cn0
    wcel
    @4
    @41
    @2
    @3
    cE
    dmfi
    ad2antll
    @6
    @40
    @42
    @1
    @40
    @42
    wi
    @0
    @5
    @1
    @40
    @42
    @1
    @31
    cV
    @7
    @35
    eleq2d
    biimpd
    ad2antlr
    imp
    @26
    @7
    cG
    cE
    cV
    finsumvtxdg2sstep.v
    finsumvtxdg2sstep.e
    @26
    eqid
    vtxdgfisnn0
    syl2an2r
    nn0zd
    ralrimiva
    @19
    @11
    vv
    cV
    cN
    fsumsplitsnun
    syl121anc
    @6
    @33
    @21
    @20
    caddc
    @2
    @33
    @21
    wceq
    @5
    @2
    vv
    cN
    @11
    @21
    cV
    @39
    @7
    cN
    wceq
    @11
    @21
    wceq
    @2
    @7
    cN
    @10
    fveq2
    adantl
    csbied
    adantr
    oveq2d
    3eqtrd
    adantr
    @17
    @22
    @20
    cN
    vj
    cv
    #
    cE
    cfv
    #
    wcel
    #
    vj
    @26
    crab
    #
    chash
    cfv
    #
    @24
    @18
    wceq
    vi
    @26
    crab
    chash
    cfv
    caddc
    co
    #
    caddc
    co
    #
    c2
    @8
    @47
    caddc
    co
    #
    cmul
    co
    #
    @30
    @6
    @22
    @49
    wceq
    @9
    @6
    @21
    @48
    @20
    caddc
    cP
    cS
    vi
    cE
    cG
    cI
    @46
    cK
    cN
    cV
    finsumvtxdg2sstep.v
    finsumvtxdg2sstep.e
    finsumvtxdg2sstep.k
    finsumvtxdg2sstep.i
    finsumvtxdg2sstep.p
    finsumvtxdg2sstep.s
    @45
    @25
    vj
    vi
    @26
    @43
    @23
    wceq
    @44
    @24
    cN
    @43
    @23
    cE
    fveq2
    eleq2d
    cbvrabv
    #
    finsumvtxdg2ssteplem2
    oveq2d
    adantr
    vv
    cP
    cS
    vi
    cE
    cG
    cI
    @46
    cK
    cN
    cV
    finsumvtxdg2sstep.v
    finsumvtxdg2sstep.e
    finsumvtxdg2sstep.k
    finsumvtxdg2sstep.i
    finsumvtxdg2sstep.p
    finsumvtxdg2sstep.s
    @52
    finsumvtxdg2ssteplem4
    @51
    @30
    wceq
    @17
    @50
    @29
    c2
    cmul
    @47
    @28
    @8
    caddc
    @46
    @27
    chash
    @52
    fveq2i
    oveq2i
    oveq2i
    a1i
    3eqtrd
    @6
    @30
    @14
    wceq
    @9
    @6
    @14
    @30
    @6
    @13
    @29
    c2
    cmul
    cP
    cS
    vi
    cE
    cG
    cI
    @27
    cK
    cN
    cV
    finsumvtxdg2sstep.v
    finsumvtxdg2sstep.e
    finsumvtxdg2sstep.k
    finsumvtxdg2sstep.i
    finsumvtxdg2sstep.p
    finsumvtxdg2sstep.s
    @27
    eqid
    finsumvtxdg2ssteplem1
    oveq2d
    eqcomd
    adantr
    3eqtrd
    ex
    embantd
end
