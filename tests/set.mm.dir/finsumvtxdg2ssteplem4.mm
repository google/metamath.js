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
include "csn.mm"
include "cdif.mm"
include "cdm.mm"
include "crab.mm"
include "caddc.mm"
include "wral.mm"
include "vtxdginducedm1fi.mm"
include "ad2antll.mm"
include "sumeq2d.mm"
include "diffi.mm"
include "adantr.mm"
include "adantl.mm"
include "cc.mm"
include "cres.mm"
include "dmeqi.mm"
include "finresfin.mm"
include "dmfi.mm"
include "syl.mm"
include "syl5eqel.mm"
include "eqcomi.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "cvtx.mm"
include "cop.mm"
include "fveq2i.mm"
include "cvv.mm"
include "fvexi.mm"
include "difexi.mm"
include "eqeltri.mm"
include "ciedg.mm"
include "resex.mm"
include "opvtxfvi.mm"
include "eqtr2i.mm"
include "vtxdginducedm1lem1.mm"
include "eqid.mm"
include "vtxdgfisnn0.mm"
include "nn0cnd.mm"
include "syl2an.mm"
include "cn0.mm"
include "rabfi.mm"
include "hashcl.mm"
include "3syl.mm"
include "fsumadd.mm"
include "eqtrd.mm"
include "sumeq1i.mm"
include "eqeq1i.mm"
include "oveq1.mm"
include "sylbi.mm"
include "sylan9eq.mm"
include "oveq1d.mm"
include "fsumcl.mm"
include "add12d.mm"
include "finsumvtxdg2ssteplem3.mm"
include "oveq2d.mm"
include "2timesd.mm"
include "eqcomd.mm"
include "3eqtrd.mm"
include "2cnd.mm"
include "mulcld.mm"
include "addcld.mm"
include "addassd.mm"
include "adddid.mm"
include "3eqtr4d.mm"

theorem finsumvtxdg2ssteplem4
  let vv: setvar v
  let cP: class P
  let cS: class S
  let vi: setvar i
  let cE: class E
  let cG: class G
  let cI: class I
  let cJ: class J
  let cK: class K
  let cN: class N
  let cV: class V
  assume finsumvtxdg2sstep.v: |- V = ( Vtx ` G )
  assume finsumvtxdg2sstep.e: |- E = ( iEdg ` G )
  assume finsumvtxdg2sstep.k: |- K = ( V \ { N } )
  assume finsumvtxdg2sstep.i: |- I = { i e. dom E | N e/ ( E ` i ) }
  assume finsumvtxdg2sstep.p: |- P = ( E |` I )
  assume finsumvtxdg2sstep.s: |- S = <. K , P >.
  assume finsumvtxdg2ssteplem.j: |- J = { i e. dom E | N e. ( E ` i ) }

  disjoint E v
  disjoint G v
  disjoint N v
  disjoint V i
  disjoint V v
  disjoint i v
  disjoint J i
  disjoint K v
  disjoint E i
  disjoint G i
  disjoint N i
  assert |- ( ( ( ( G e. UPGraph /\ N e. V ) /\ ( V e. Fin /\ E e. Fin ) ) /\ sum_ v e. K ( ( VtxDeg ` S ) ` v ) = ( 2 x. ( # ` P ) ) ) -> ( sum_ v e. ( V \ { N } ) ( ( VtxDeg ` G ) ` v ) + ( ( # ` J ) + ( # ` { i e. dom E | ( E ` i ) = { N } } ) ) ) = ( 2 x. ( ( # ` P ) + ( # ` J ) ) ) )

  proof
    cG
    cupgr
    wcel
    cN
    cV
    wcel
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
    cK
    vv
    cv
    #
    cS
    cvtxdg
    cfv
    cfv
    #
    vv
    csu
    #
    c2
    cP
    chash
    cfv
    #
    cmul
    co
    #
    wceq
    #
    wa
    #
    cV
    cN
    csn
    #
    cdif
    #
    @5
    cG
    cvtxdg
    cfv
    cfv
    #
    vv
    csu
    #
    cJ
    chash
    cfv
    #
    vi
    cv
    cE
    cfv
    #
    @12
    wceq
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
    caddc
    co
    @9
    @13
    @5
    @17
    wcel
    #
    vi
    cJ
    crab
    #
    chash
    cfv
    #
    vv
    csu
    #
    caddc
    co
    #
    @22
    caddc
    co
    #
    c2
    @8
    @16
    caddc
    co
    cmul
    co
    #
    @11
    @15
    @27
    @22
    caddc
    @4
    @10
    @15
    @13
    @6
    vv
    csu
    #
    @26
    caddc
    co
    #
    @27
    @4
    @15
    @13
    @6
    @25
    caddc
    co
    #
    vv
    csu
    @31
    @4
    @13
    @14
    @32
    vv
    @2
    @14
    @32
    wceq
    vv
    @13
    wral
    @0
    @1
    vv
    cP
    cS
    vi
    cE
    cG
    cI
    cJ
    cK
    cN
    cV
    vi
    finsumvtxdg2sstep.v
    finsumvtxdg2sstep.e
    finsumvtxdg2sstep.k
    finsumvtxdg2sstep.i
    finsumvtxdg2sstep.p
    finsumvtxdg2sstep.s
    finsumvtxdg2ssteplem.j
    vtxdginducedm1fi
    ad2antll
    sumeq2d
    @4
    @13
    @6
    @25
    vv
    @3
    @13
    cfn
    wcel
    #
    @0
    @1
    @33
    @2
    cV
    @12
    diffi
    adantr
    #
    adantl
    @4
    cP
    cdm
    #
    cfn
    wcel
    #
    @5
    cK
    wcel
    #
    @6
    cc
    wcel
    @5
    @13
    wcel
    #
    @2
    @36
    @0
    @1
    @2
    @35
    cE
    cI
    cres
    #
    cdm
    #
    cfn
    cP
    @39
    finsumvtxdg2sstep.p
    dmeqi
    @2
    @39
    cfn
    wcel
    @40
    cfn
    wcel
    cI
    cE
    finresfin
    #
    @39
    dmfi
    syl
    syl5eqel
    ad2antll
    @38
    @37
    @13
    cK
    @5
    cK
    @13
    finsumvtxdg2sstep.k
    eqcomi
    eleq2i
    biimpi
    @36
    @37
    wa
    @6
    @35
    @5
    cS
    cP
    cK
    cS
    cvtx
    cfv
    cK
    cP
    cop
    #
    cvtx
    cfv
    cK
    cS
    @42
    cvtx
    finsumvtxdg2sstep.s
    fveq2i
    cP
    cK
    cK
    @13
    cvv
    finsumvtxdg2sstep.k
    cV
    @12
    cV
    cG
    cvtx
    finsumvtxdg2sstep.v
    fvexi
    difexi
    eqeltri
    cP
    @39
    cvv
    finsumvtxdg2sstep.p
    cE
    cI
    cE
    cG
    ciedg
    finsumvtxdg2sstep.e
    fvexi
    resex
    eqeltri
    opvtxfvi
    eqtr2i
    cS
    ciedg
    cfv
    cP
    cP
    cS
    vi
    cE
    cG
    cI
    cK
    cN
    cV
    finsumvtxdg2sstep.v
    finsumvtxdg2sstep.e
    finsumvtxdg2sstep.k
    finsumvtxdg2sstep.i
    finsumvtxdg2sstep.p
    finsumvtxdg2sstep.s
    vtxdginducedm1lem1
    eqcomi
    @35
    eqid
    vtxdgfisnn0
    nn0cnd
    syl2an
    @4
    @25
    cc
    wcel
    #
    @38
    @2
    @43
    @0
    @1
    @2
    @25
    @2
    cJ
    cfn
    wcel
    #
    @24
    cfn
    wcel
    @25
    cn0
    wcel
    @2
    cJ
    cN
    @17
    wcel
    #
    vi
    @19
    crab
    #
    cfn
    finsumvtxdg2ssteplem.j
    @2
    @19
    cfn
    wcel
    #
    @46
    cfn
    wcel
    cE
    dmfi
    #
    @45
    vi
    @19
    rabfi
    syl
    syl5eqel
    #
    @23
    vi
    cJ
    rabfi
    @24
    hashcl
    3syl
    nn0cnd
    #
    ad2antll
    adantr
    fsumadd
    eqtrd
    @10
    @30
    @9
    wceq
    @31
    @27
    wceq
    @7
    @30
    @9
    cK
    @13
    @6
    vv
    finsumvtxdg2sstep.k
    sumeq1i
    eqeq1i
    @30
    @9
    @26
    caddc
    oveq1
    sylbi
    sylan9eq
    oveq1d
    @4
    @28
    @29
    wceq
    @10
    @4
    @9
    @26
    @22
    caddc
    co
    #
    caddc
    co
    @9
    c2
    @16
    cmul
    co
    #
    caddc
    co
    @28
    @29
    @4
    @51
    @52
    @9
    caddc
    @4
    @51
    @16
    @26
    @21
    caddc
    co
    #
    caddc
    co
    #
    @16
    @16
    caddc
    co
    #
    @52
    @3
    @51
    @54
    wceq
    @0
    @3
    @26
    @16
    @21
    @3
    @13
    @25
    vv
    @34
    @3
    @43
    @38
    @2
    @43
    @1
    @50
    adantl
    adantr
    fsumcl
    #
    @2
    @16
    cc
    wcel
    #
    @1
    @2
    @16
    @2
    @44
    @16
    cn0
    wcel
    @49
    cJ
    hashcl
    syl
    nn0cnd
    #
    adantl
    @2
    @21
    cc
    wcel
    @1
    @2
    @21
    @2
    @47
    @20
    cfn
    wcel
    @21
    cn0
    wcel
    @48
    @18
    vi
    @19
    rabfi
    @20
    hashcl
    3syl
    nn0cnd
    #
    adantl
    add12d
    adantl
    @4
    @53
    @16
    @16
    caddc
    vv
    cP
    cS
    vi
    cE
    cG
    cI
    cJ
    cK
    cN
    cV
    finsumvtxdg2sstep.v
    finsumvtxdg2sstep.e
    finsumvtxdg2sstep.k
    finsumvtxdg2sstep.i
    finsumvtxdg2sstep.p
    finsumvtxdg2sstep.s
    finsumvtxdg2ssteplem.j
    finsumvtxdg2ssteplem3
    oveq2d
    @2
    @55
    @52
    wceq
    @0
    @1
    @2
    @52
    @55
    @2
    @16
    @58
    2timesd
    eqcomd
    ad2antll
    3eqtrd
    oveq2d
    @4
    @9
    @26
    @22
    @2
    @9
    cc
    wcel
    @0
    @1
    @2
    c2
    @8
    @2
    2cnd
    @2
    @8
    @2
    cP
    cfn
    wcel
    @8
    cn0
    wcel
    @2
    cP
    @39
    cfn
    finsumvtxdg2sstep.p
    @41
    syl5eqel
    cP
    hashcl
    syl
    nn0cnd
    #
    mulcld
    ad2antll
    @3
    @26
    cc
    wcel
    @0
    @56
    adantl
    @2
    @22
    cc
    wcel
    @0
    @1
    @2
    @16
    @21
    @58
    @59
    addcld
    ad2antll
    addassd
    @4
    c2
    @8
    @16
    @4
    2cnd
    @2
    @8
    cc
    wcel
    @0
    @1
    @60
    ad2antll
    @2
    @57
    @0
    @1
    @58
    ad2antll
    adddid
    3eqtr4d
    adantr
    eqtrd
end
