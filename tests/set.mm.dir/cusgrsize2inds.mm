include "ccusgr.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cn0.mm"
include "csn.mm"
include "cdif.mm"
include "c2.mm"
include "cbc.mm"
include "co.mm"
include "wi.mm"
include "cvv.mm"
include "cvtx.mm"
include "fvex.mm"
include "eqeltri.mm"
include "wa.mm"
include "cn.mm"
include "hashnn0n0nn.mm"
include "anassrs.mm"
include "c1.mm"
include "cmin.mm"
include "caddc.mm"
include "simplll.mm"
include "simplr.mm"
include "wb.mm"
include "eleq1.mm"
include "eqcoms.mm"
include "nnm1nn0.mm"
include "syl6bi.mm"
include "ad2antlr.mm"
include "imp.mm"
include "nncn.mm"
include "1cnd.mm"
include "npcand.mm"
include "eqcomd.mm"
include "brfi1indlem.mm"
include "syl31anc.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "cfn.mm"
include "nnnn0.mm"
include "hashclb.mm"
include "syl5ibrcom.mm"
include "cusgrsizeinds.mm"
include "oveq2.mm"
include "adantl.mm"
include "bcn2m1.mm"
include "biimpd.mm"
include "adantr.mm"
include "sylbid.mm"
include "ex.mm"
include "com3r.mm"
include "syl.mm"
include "3exp.mm"
include "com14.mm"
include "syldc.mm"
include "com23.mm"
include "com13.mm"
include "com24.mm"
include "mpcom.mm"
include "adantllr.mm"
include "mpd.mm"
include "exp41.mm"
include "com25.mm"
include "ax-mp.mm"
include "3imp.mm"
include "com12.mm"

theorem cusgrsize2inds
  let ve: setvar e
  let cE: class E
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let cY: class Y
  let vf: setvar f
  let vn: setvar n
  assume cusgrsizeindb0.v: |- V = ( Vtx ` G )
  assume cusgrsizeindb0.e: |- E = ( Edg ` G )
  assume cusgrsizeinds.f: |- F = { e e. E | N e/ e }

  disjoint E e
  disjoint G e
  disjoint N e
  disjoint V e
  disjoint E f
  disjoint E n
  disjoint e f
  disjoint e n
  disjoint f n
  disjoint G f
  disjoint G n
  disjoint N f
  disjoint N n
  disjoint V f
  disjoint V n
  assert |- ( Y e. NN0 -> ( ( G e. ComplUSGraph /\ ( # ` V ) = Y /\ N e. V ) -> ( ( # ` F ) = ( ( # ` ( V \ { N } ) ) _C 2 ) -> ( # ` E ) = ( ( # ` V ) _C 2 ) ) ) )

  proof
    cG
    ccusgr
    wcel
    #
    cV
    chash
    cfv
    #
    cY
    wceq
    #
    cN
    cV
    wcel
    #
    w3a
    cY
    cn0
    wcel
    #
    cF
    chash
    cfv
    #
    cV
    cN
    csn
    cdif
    chash
    cfv
    #
    c2
    cbc
    co
    #
    wceq
    #
    cE
    chash
    cfv
    #
    @1
    c2
    cbc
    co
    #
    wceq
    #
    wi
    #
    @0
    @2
    @3
    @4
    @12
    wi
    #
    cV
    cvv
    wcel
    #
    @0
    @2
    @3
    @13
    wi
    wi
    wi
    cV
    cG
    cvtx
    cfv
    cvv
    cusgrsizeindb0.v
    cG
    cvtx
    fvex
    eqeltri
    @14
    @4
    @2
    @3
    @0
    @12
    @14
    @4
    @2
    @3
    @0
    @12
    wi
    #
    @14
    @4
    wa
    #
    @2
    wa
    @3
    wa
    cY
    cn
    wcel
    #
    @15
    @16
    @2
    @3
    @17
    cN
    cV
    cvv
    cY
    hashnn0n0nn
    anassrs
    @14
    @2
    @3
    @17
    @15
    wi
    @4
    @14
    @2
    wa
    #
    @3
    wa
    #
    @17
    @15
    @6
    @1
    c1
    cmin
    co
    #
    wceq
    #
    @19
    @17
    wa
    #
    @15
    @22
    @14
    @3
    @20
    cn0
    wcel
    #
    @1
    @20
    c1
    caddc
    co
    #
    wceq
    #
    @21
    @14
    @2
    @3
    @17
    simplll
    @18
    @3
    @17
    simplr
    @19
    @17
    @23
    @2
    @17
    @23
    wi
    @14
    @3
    @2
    @17
    @1
    cn
    wcel
    #
    @23
    @17
    @26
    wb
    #
    cY
    @1
    cY
    @1
    cn
    eleq1
    eqcoms
    #
    @1
    nnm1nn0
    syl6bi
    ad2antlr
    imp
    @19
    @17
    @25
    @2
    @17
    @25
    wi
    @14
    @3
    @2
    @17
    @26
    @25
    @28
    @26
    @24
    @1
    @26
    @1
    c1
    @1
    nncn
    @26
    1cnd
    npcand
    eqcomd
    syl6bi
    ad2antlr
    imp
    @14
    @3
    @23
    w3a
    @25
    @21
    cN
    cV
    cvv
    @20
    brfi1indlem
    imp
    syl31anc
    @21
    @8
    @0
    @22
    @11
    @21
    @8
    @5
    @20
    c2
    cbc
    co
    #
    wceq
    #
    @0
    @22
    @11
    wi
    wi
    @21
    @7
    @29
    @5
    @6
    @20
    c2
    cbc
    oveq1
    eqeq2d
    @22
    @0
    @30
    @11
    @19
    @17
    @0
    @30
    @11
    wi
    #
    wi
    #
    @19
    @17
    @26
    @32
    @2
    @27
    @14
    @3
    @28
    ad2antlr
    @18
    @3
    @26
    @32
    wi
    #
    @14
    @3
    @33
    wi
    @2
    @14
    @26
    @3
    @32
    @26
    @14
    cV
    cfn
    wcel
    #
    @3
    @32
    wi
    @26
    @34
    @14
    @1
    cn0
    wcel
    @1
    nnnn0
    cV
    cvv
    hashclb
    syl5ibrcom
    @0
    @34
    @3
    @26
    @31
    @0
    @34
    @3
    @26
    @31
    wi
    #
    @0
    @34
    @3
    w3a
    @9
    @20
    @5
    caddc
    co
    #
    wceq
    #
    @35
    ve
    cE
    cF
    cG
    cN
    cV
    cusgrsizeindb0.v
    cusgrsizeindb0.e
    cusgrsizeinds.f
    cusgrsizeinds
    @26
    @30
    @37
    @11
    @26
    @30
    @37
    @11
    wi
    @26
    @30
    wa
    @37
    @9
    @20
    @29
    caddc
    co
    #
    wceq
    #
    @11
    @30
    @37
    @39
    wb
    @26
    @30
    @36
    @38
    @9
    @5
    @29
    @20
    caddc
    oveq2
    eqeq2d
    adantl
    @26
    @39
    @11
    wi
    @30
    @26
    @39
    @11
    @26
    @38
    @10
    @9
    @1
    bcn2m1
    eqeq2d
    biimpd
    adantr
    sylbid
    ex
    com3r
    syl
    3exp
    com14
    syldc
    com23
    adantr
    imp
    sylbid
    imp
    com13
    syl6bi
    com24
    mpcom
    ex
    adantllr
    mpd
    exp41
    com25
    ax-mp
    3imp
    com12
end
