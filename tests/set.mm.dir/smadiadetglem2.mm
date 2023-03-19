include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "w3a.mm"
include "csn.mm"
include "cxp.mm"
include "cv.mm"
include "wceq.mm"
include "cur.mm"
include "c0g.mm"
include "cif.mm"
include "cmpt2.mm"
include "cof.mm"
include "co.mm"
include "cminmar1.mm"
include "cres.mm"
include "cmarrep.mm"
include "cvv.mm"
include "snex.mm"
include "a1i.mm"
include "cfn.mm"
include "wa.mm"
include "matrcl.mm"
include "elex.mm"
include "adantr.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "simp13.mm"
include "crg.mm"
include "ccrg.mm"
include "crngring.mm"
include "mp1i.mm"
include "eqid.mm"
include "ringidcl.mm"
include "ring0cl.mm"
include "ifcld.mm"
include "fconstmpt2.mm"
include "eqidd.mm"
include "offval22.mm"
include "ringridm.mm"
include "mpancom.mm"
include "3ad2ant3.mm"
include "ad2antrl.mm"
include "iftrue.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "wn.mm"
include "ringrz.mm"
include "iffalse.mm"
include "pm2.61ian.mm"
include "3adant2.mm"
include "mpt2eq3dva.mm"
include "eqtrd.mm"
include "simp2.mm"
include "minmar1val.mm"
include "syld3an3.mm"
include "reseq1d.mm"
include "wss.mm"
include "snssi.mm"
include "3ad2ant2.mm"
include "ssid.mm"
include "resmpt2.mm"
include "sylancl.mm"
include "mpt2snif.mm"
include "3eqtrd.mm"
include "3simpb.mm"
include "marrepval.mm"
include "syl12anc.mm"
include "3eqtr4rd.mm"

theorem smadiadetglem2
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cE: class E
  let cK: class K
  let cM: class M
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  assume smadiadet.a: |- A = ( N Mat R )
  assume smadiadet.b: |- B = ( Base ` A )
  assume smadiadet.r: |- R e. CRing
  assume smadiadet.d: |- D = ( N maDet R )
  assume smadiadet.h: |- E = ( ( N \ { K } ) maDet R )
  assume smadiadetg.x: |- .x. = ( .r ` R )


  assert |- ( ( M e. B /\ K e. N /\ S e. ( Base ` R ) ) -> ( ( K ( M ( N matRRep R ) S ) K ) |` ( { K } X. N ) ) = ( ( ( { K } X. N ) X. { S } ) oF .x. ( ( K ( ( N minMatR1 R ) ` M ) K ) |` ( { K } X. N ) ) ) )

  proof
    cM
    cB
    wcel
    #
    cK
    cN
    wcel
    #
    cS
    cR
    cbs
    cfv
    #
    wcel
    #
    w3a
    #
    cK
    csn
    #
    cN
    cxp
    #
    cS
    csn
    cxp
    #
    vi
    vj
    @5
    cN
    vj
    cv
    #
    cK
    wceq
    #
    cR
    cur
    cfv
    #
    cR
    c0g
    cfv
    #
    cif
    #
    cmpt2
    #
    c.x
    cof
    #
    co
    #
    vi
    vj
    @5
    cN
    @9
    cS
    @11
    cif
    #
    cmpt2
    #
    @7
    cK
    cK
    cM
    cN
    cR
    cminmar1
    co
    #
    cfv
    co
    #
    @6
    cres
    #
    @14
    co
    cK
    cK
    cM
    cS
    cN
    cR
    cmarrep
    co
    #
    co
    co
    #
    @6
    cres
    #
    @4
    @15
    vi
    vj
    @5
    cN
    cS
    @12
    c.x
    co
    #
    cmpt2
    @17
    @4
    vi
    vj
    @5
    cN
    cS
    @12
    c.x
    @7
    @13
    cvv
    cvv
    @2
    @2
    @5
    cvv
    wcel
    @4
    cK
    snex
    a1i
    @0
    @1
    cN
    cvv
    wcel
    #
    @3
    @0
    cN
    cfn
    wcel
    #
    cR
    cvv
    wcel
    #
    wa
    @25
    cA
    cB
    cR
    cN
    cM
    smadiadet.a
    smadiadet.b
    matrcl
    @26
    @25
    @27
    cN
    cfn
    elex
    adantr
    syl
    3ad2ant1
    @0
    @1
    @3
    vi
    cv
    #
    @5
    wcel
    #
    @8
    cN
    wcel
    #
    simp13
    @4
    @29
    @30
    w3a
    #
    cR
    crg
    wcel
    #
    @12
    @2
    wcel
    cR
    ccrg
    wcel
    #
    @32
    @31
    smadiadet.r
    cR
    crngring
    #
    mp1i
    @32
    @9
    @10
    @11
    @2
    @2
    cR
    @10
    @2
    eqid
    #
    @10
    eqid
    #
    ringidcl
    @2
    cR
    @11
    @35
    @11
    eqid
    #
    ring0cl
    ifcld
    syl
    @7
    vi
    vj
    @5
    cN
    cS
    cmpt2
    wceq
    @4
    vi
    vj
    @5
    cN
    cS
    fconstmpt2
    a1i
    @4
    @13
    eqidd
    offval22
    @4
    vi
    vj
    @5
    cN
    @24
    @16
    @4
    @30
    @24
    @16
    wceq
    #
    @29
    @9
    @4
    @30
    wa
    #
    @38
    @9
    @39
    wa
    #
    cS
    @10
    c.x
    co
    #
    cS
    @24
    @16
    @4
    @41
    cS
    wceq
    #
    @9
    @30
    @3
    @0
    @42
    @1
    @32
    @3
    @42
    @33
    @32
    @3
    smadiadet.r
    @34
    mp1i
    #
    @2
    cR
    c.x
    @10
    cS
    @35
    smadiadetg.x
    @36
    ringridm
    mpancom
    3ad2ant3
    ad2antrl
    @40
    @12
    @10
    cS
    c.x
    @9
    @12
    @10
    wceq
    @39
    @9
    @10
    @11
    iftrue
    adantr
    oveq2d
    @9
    @16
    cS
    wceq
    @39
    @9
    cS
    @11
    iftrue
    adantr
    3eqtr4d
    @9
    wn
    #
    @39
    wa
    cS
    @11
    c.x
    co
    #
    @11
    @24
    @16
    @4
    @45
    @11
    wceq
    #
    @44
    @30
    @3
    @0
    @46
    @1
    @32
    @3
    @46
    @43
    @2
    cR
    c.x
    cS
    @11
    @35
    smadiadetg.x
    @37
    ringrz
    mpancom
    3ad2ant3
    ad2antrl
    @44
    @24
    @45
    wceq
    @39
    @44
    @12
    @11
    cS
    c.x
    @9
    @10
    @11
    iffalse
    oveq2d
    adantr
    @44
    @16
    @11
    wceq
    @39
    @9
    cS
    @11
    iffalse
    adantr
    3eqtr4d
    pm2.61ian
    3adant2
    mpt2eq3dva
    eqtrd
    @4
    @20
    @13
    @7
    @14
    @4
    @20
    vi
    vj
    cN
    cN
    @28
    cK
    wceq
    #
    @12
    @28
    @8
    cM
    co
    #
    cif
    #
    cmpt2
    #
    @6
    cres
    #
    vi
    vj
    @5
    cN
    @49
    cmpt2
    #
    @13
    @4
    @19
    @50
    @6
    @0
    @1
    @3
    @1
    @19
    @50
    wceq
    @0
    @1
    @3
    simp2
    #
    cA
    cB
    @18
    cR
    @10
    vi
    vj
    cK
    cK
    cM
    cN
    @11
    smadiadet.a
    smadiadet.b
    @18
    eqid
    @36
    @37
    minmar1val
    syld3an3
    reseq1d
    @4
    @5
    cN
    wss
    #
    cN
    cN
    wss
    #
    @51
    @52
    wceq
    @1
    @0
    @54
    @3
    cK
    cN
    snssi
    3ad2ant2
    #
    cN
    ssid
    #
    vi
    vj
    cN
    cN
    @5
    cN
    @49
    resmpt2
    sylancl
    @52
    @13
    wceq
    @4
    cN
    @12
    @48
    vi
    vj
    cK
    mpt2snif
    a1i
    3eqtrd
    oveq2d
    @4
    @23
    vi
    vj
    cN
    cN
    @47
    @16
    @48
    cif
    #
    cmpt2
    #
    @6
    cres
    #
    vi
    vj
    @5
    cN
    @58
    cmpt2
    #
    @17
    @4
    @22
    @59
    @6
    @4
    @0
    @3
    wa
    @1
    @1
    @22
    @59
    wceq
    @0
    @1
    @3
    3simpb
    @53
    @53
    cA
    cB
    @21
    cR
    cS
    vi
    vj
    cK
    cK
    cM
    cN
    @11
    smadiadet.a
    smadiadet.b
    @21
    eqid
    @37
    marrepval
    syl12anc
    reseq1d
    @4
    @54
    @55
    @60
    @61
    wceq
    @56
    @57
    vi
    vj
    cN
    cN
    @5
    cN
    @58
    resmpt2
    sylancl
    @61
    @17
    wceq
    @4
    cN
    @16
    @48
    vi
    vj
    cK
    mpt2snif
    a1i
    3eqtrd
    3eqtr4rd
end
