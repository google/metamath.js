include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cn0.mm"
include "cv.mm"
include "cdecpmat.mm"
include "co.mm"
include "cvsca.mm"
include "cfv.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "cgsu.mm"
include "crg.mm"
include "wceq.mm"
include "crngring.mm"
include "eqid.mm"
include "pmatcollpw2.mm"
include "syl3an2.mm"
include "wa.mm"
include "wral.mm"
include "cbs.mm"
include "eqidd.mm"
include "oveq12.mm"
include "oveq1d.mm"
include "adantl.mm"
include "simprl.mm"
include "simpr.mm"
include "simp2.mm"
include "adantr.mm"
include "syl.mm"
include "cmat.mm"
include "simp3.mm"
include "decpmatcl.mm"
include "syl3anc.mm"
include "matecld.mm"
include "simplr.mm"
include "cmgp.mm"
include "ply1tmcl.mm"
include "ovmpt2d.mm"
include "pmatcollpwlem.mm"
include "3expb.mm"
include "eqtrd.mm"
include "ralrimivva.mm"
include "wb.mm"
include "simpl1.mm"
include "ply1ring.mm"
include "3ad2ant2.mm"
include "3ad2ant1.mm"
include "matbas2d.mm"
include "ply1moncl.mm"
include "sylan.mm"
include "mat2pmatbas.mm"
include "syl6eleqr.mm"
include "matvscl.mm"
include "syl22anc.mm"
include "eqmat.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"

theorem pmatcollpw
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cT: class T
  let vn: setvar n
  let c.ex: class .^
  let c.as: class .*
  let cM: class M
  let cN: class N
  let cX: class X
  let vi: setvar i
  let vj: setvar j
  let va: setvar a
  let vb: setvar b
  assume pmatcollpw.p: |- P = ( Poly1 ` R )
  assume pmatcollpw.c: |- C = ( N Mat P )
  assume pmatcollpw.b: |- B = ( Base ` C )
  assume pmatcollpw.m: |- .* = ( .s ` C )
  assume pmatcollpw.e: |- .^ = ( .g ` ( mulGrp ` P ) )
  assume pmatcollpw.x: |- X = ( var1 ` R )
  assume pmatcollpw.t: |- T = ( N matToPolyMat R )

  disjoint B n
  disjoint M n
  disjoint N n
  disjoint P n
  disjoint R n
  disjoint X n
  disjoint .^ n
  disjoint B i
  disjoint B j
  disjoint i j
  disjoint M i
  disjoint M j
  disjoint N i
  disjoint N j
  disjoint P i
  disjoint P j
  disjoint R i
  disjoint R j
  disjoint a i
  disjoint a j
  disjoint b i
  disjoint b j
  disjoint i n
  disjoint j n
  disjoint B a
  disjoint B b
  disjoint a b
  disjoint a n
  disjoint b n
  disjoint M a
  disjoint M b
  disjoint N a
  disjoint N b
  disjoint P a
  disjoint P b
  disjoint R a
  disjoint R b
  disjoint T a
  disjoint T b
  disjoint X a
  disjoint X b
  disjoint X i
  disjoint X j
  disjoint .* a
  disjoint .* b
  disjoint .^ a
  disjoint .^ b
  disjoint .^ i
  disjoint .^ j
  assert |- ( ( N e. Fin /\ R e. CRing /\ M e. B ) -> M = ( C gsum ( n e. NN0 |-> ( ( n .^ X ) .* ( T ` ( M decompPMat n ) ) ) ) ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    ccrg
    wcel
    #
    cM
    cB
    wcel
    #
    w3a
    #
    cM
    cC
    vn
    cn0
    vi
    vj
    cN
    cN
    vi
    cv
    #
    vj
    cv
    #
    cM
    vn
    cv
    #
    cdecpmat
    co
    #
    co
    #
    @6
    cX
    c.ex
    co
    #
    cP
    cvsca
    cfv
    #
    co
    #
    cmpt2
    #
    cmpt
    #
    cgsu
    co
    #
    cC
    vn
    cn0
    @9
    @7
    cT
    cfv
    #
    c.as
    co
    #
    cmpt
    #
    cgsu
    co
    @1
    @0
    cR
    crg
    wcel
    #
    @2
    cM
    @14
    wceq
    cR
    crngring
    #
    cB
    cC
    cP
    cR
    @10
    vi
    vj
    vn
    c.ex
    cM
    cN
    cX
    pmatcollpw.p
    pmatcollpw.c
    pmatcollpw.b
    @10
    eqid
    #
    pmatcollpw.e
    pmatcollpw.x
    pmatcollpw2
    syl3an2
    @3
    @13
    @17
    cC
    cgsu
    @3
    vn
    cn0
    @12
    @16
    @3
    @6
    cn0
    wcel
    #
    wa
    #
    @12
    @16
    wceq
    #
    va
    cv
    #
    vb
    cv
    #
    @12
    co
    #
    @24
    @25
    @16
    co
    #
    wceq
    #
    vb
    cN
    wral
    va
    cN
    wral
    #
    @22
    @28
    va
    vb
    cN
    cN
    @22
    @24
    cN
    wcel
    #
    @25
    cN
    wcel
    #
    wa
    #
    wa
    #
    @26
    @24
    @25
    @7
    co
    #
    @9
    @10
    co
    #
    @27
    @33
    vi
    vj
    @24
    @25
    cN
    cN
    @11
    @35
    @12
    cP
    cbs
    cfv
    #
    @33
    @12
    eqidd
    @4
    @24
    wceq
    @5
    @25
    wceq
    wa
    #
    @11
    @35
    wceq
    @33
    @37
    @8
    @34
    @9
    @10
    @4
    @24
    @5
    @25
    @7
    oveq12
    oveq1d
    adantl
    @22
    @30
    @31
    simprl
    #
    @32
    @31
    @22
    @30
    @31
    simpr
    adantl
    #
    @33
    @18
    @34
    cR
    cbs
    cfv
    #
    wcel
    @21
    @35
    @36
    wcel
    @22
    @18
    @32
    @22
    @1
    @18
    @3
    @1
    @21
    @0
    @1
    @2
    simp2
    adantr
    #
    @19
    syl
    #
    adantr
    @33
    cN
    cR
    cmat
    co
    #
    @43
    cbs
    cfv
    #
    cR
    @24
    @25
    @40
    @7
    cN
    @43
    eqid
    #
    @40
    eqid
    #
    @44
    eqid
    #
    @38
    @39
    @22
    @7
    @44
    wcel
    #
    @32
    @22
    @1
    @2
    @21
    @48
    @41
    @3
    @2
    @21
    @0
    @1
    @2
    simp3
    adantr
    @3
    @21
    simpr
    #
    @43
    cB
    cC
    @44
    cP
    cR
    @6
    cM
    cN
    ccrg
    pmatcollpw.p
    pmatcollpw.c
    pmatcollpw.b
    @45
    @47
    decpmatcl
    syl3anc
    #
    adantr
    matecld
    @3
    @21
    @32
    simplr
    @36
    @34
    @6
    cP
    cR
    @10
    c.ex
    @40
    cP
    cmgp
    cfv
    #
    cX
    @46
    pmatcollpw.p
    pmatcollpw.x
    @20
    @51
    eqid
    #
    pmatcollpw.e
    @36
    eqid
    #
    ply1tmcl
    syl3anc
    ovmpt2d
    @22
    @30
    @31
    @35
    @27
    wceq
    cB
    cC
    cP
    cR
    cT
    vn
    c.ex
    c.as
    cM
    cN
    cX
    va
    vb
    pmatcollpw.p
    pmatcollpw.c
    pmatcollpw.b
    pmatcollpw.m
    pmatcollpw.e
    pmatcollpw.x
    pmatcollpw.t
    pmatcollpwlem
    3expb
    eqtrd
    ralrimivva
    @22
    @12
    cB
    wcel
    @16
    cB
    wcel
    #
    @23
    @29
    wb
    @22
    vi
    vj
    cC
    cB
    @11
    cP
    @36
    cN
    crg
    pmatcollpw.c
    @53
    pmatcollpw.b
    @0
    @1
    @2
    @21
    simpl1
    #
    @3
    cP
    crg
    wcel
    #
    @21
    @1
    @0
    @56
    @2
    @1
    @18
    @56
    @19
    cP
    cR
    pmatcollpw.p
    ply1ring
    syl
    3ad2ant2
    adantr
    #
    @22
    @4
    cN
    wcel
    #
    @5
    cN
    wcel
    #
    w3a
    #
    @18
    @8
    @40
    wcel
    @21
    @11
    @36
    wcel
    @22
    @58
    @18
    @59
    @42
    3ad2ant1
    @60
    @43
    @44
    cR
    @4
    @5
    @40
    @7
    cN
    @45
    @46
    @47
    @22
    @58
    @59
    simp2
    @22
    @58
    @59
    simp3
    @22
    @58
    @48
    @59
    @50
    3ad2ant1
    matecld
    @22
    @58
    @21
    @59
    @49
    3ad2ant1
    @36
    @8
    @6
    cP
    cR
    @10
    c.ex
    @40
    @51
    cX
    @46
    pmatcollpw.p
    pmatcollpw.x
    @20
    @52
    pmatcollpw.e
    @53
    ply1tmcl
    syl3anc
    matbas2d
    @22
    @0
    @56
    @9
    @36
    wcel
    #
    @15
    cB
    wcel
    @54
    @55
    @57
    @3
    @18
    @21
    @61
    @1
    @0
    @18
    @2
    @19
    3ad2ant2
    #
    @36
    @6
    cP
    cR
    c.ex
    @51
    cX
    pmatcollpw.p
    pmatcollpw.x
    @52
    pmatcollpw.e
    @53
    ply1moncl
    sylan
    @22
    @15
    cC
    cbs
    cfv
    #
    cB
    @22
    @0
    @18
    @48
    @15
    @63
    wcel
    @55
    @3
    @18
    @21
    @62
    adantr
    @50
    @43
    @44
    cC
    cP
    cR
    cT
    @7
    cN
    pmatcollpw.t
    @45
    @47
    pmatcollpw.p
    pmatcollpw.c
    mat2pmatbas
    syl3anc
    pmatcollpw.b
    syl6eleqr
    cC
    cB
    @9
    cP
    c.as
    @36
    cN
    @15
    @53
    pmatcollpw.c
    pmatcollpw.b
    pmatcollpw.m
    matvscl
    syl22anc
    cC
    cB
    cP
    va
    vb
    cN
    @12
    @16
    pmatcollpw.c
    pmatcollpw.b
    eqmat
    syl2anc
    mpbird
    mpteq2dva
    oveq2d
    eqtrd
end
