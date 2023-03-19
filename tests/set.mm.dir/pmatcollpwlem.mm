include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cv.mm"
include "cn0.mm"
include "wa.mm"
include "cdecpmat.mm"
include "co.mm"
include "cvsca.mm"
include "cfv.mm"
include "cascl.mm"
include "cmpt2.mm"
include "cmulr.mm"
include "casa.mm"
include "csca.mm"
include "cbs.mm"
include "wceq.mm"
include "ply1assa.mm"
include "3ad2ant2.mm"
include "adantr.mm"
include "3ad2ant1.mm"
include "cmat.mm"
include "eqid.mm"
include "simp2.mm"
include "simp3.mm"
include "simpr.mm"
include "decpmatcl.mm"
include "syl3anc.mm"
include "matecld.mm"
include "wb.mm"
include "crg.mm"
include "crngring.mm"
include "ply1sca.mm"
include "syl.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "mpbird.mm"
include "cmgp.mm"
include "ply1moncl.mm"
include "sylan.mm"
include "asclmul2.mm"
include "cvv.mm"
include "eqidd.mm"
include "oveq12.mm"
include "adantl.mm"
include "fvexd.mm"
include "ovmpt2d.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "ply1ring.mm"
include "simpl1.mm"
include "ply1sclcl.mm"
include "syl2anc.mm"
include "matbas2d.mm"
include "jca.mm"
include "matvscacell.mm"
include "mat2pmatval.mm"
include "oveqd.mm"
include "3eqtr2d.mm"

theorem pmatcollpwlem
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
  let va: setvar a
  let vb: setvar b
  let vi: setvar i
  let vj: setvar j
  assume pmatcollpw.p: |- P = ( Poly1 ` R )
  assume pmatcollpw.c: |- C = ( N Mat P )
  assume pmatcollpw.b: |- B = ( Base ` C )
  assume pmatcollpw.m: |- .* = ( .s ` C )
  assume pmatcollpw.e: |- .^ = ( .g ` ( mulGrp ` P ) )
  assume pmatcollpw.x: |- X = ( var1 ` R )
  assume pmatcollpw.t: |- T = ( N matToPolyMat R )


  assert |- ( ( ( ( N e. Fin /\ R e. CRing /\ M e. B ) /\ n e. NN0 ) /\ a e. N /\ b e. N ) -> ( ( a ( M decompPMat n ) b ) ( .s ` P ) ( n .^ X ) ) = ( a ( ( n .^ X ) .* ( T ` ( M decompPMat n ) ) ) b ) )

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
    vn
    cv
    #
    cn0
    wcel
    #
    wa
    #
    va
    cv
    #
    cN
    wcel
    #
    vb
    cv
    #
    cN
    wcel
    #
    w3a
    #
    @7
    @9
    cM
    @4
    cdecpmat
    co
    #
    co
    #
    @4
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
    @14
    @7
    @9
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
    @12
    co
    #
    cP
    cascl
    cfv
    #
    cfv
    #
    cmpt2
    #
    co
    #
    cP
    cmulr
    cfv
    #
    co
    #
    @7
    @9
    @14
    @22
    c.as
    co
    #
    co
    #
    @7
    @9
    @14
    @12
    cT
    cfv
    #
    c.as
    co
    #
    co
    #
    @11
    @14
    @13
    @20
    cfv
    #
    @24
    co
    #
    @16
    @25
    @11
    cP
    casa
    wcel
    #
    @13
    cP
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    #
    @14
    cP
    cbs
    cfv
    #
    wcel
    #
    @32
    @16
    wceq
    @6
    @8
    @33
    @10
    @3
    @33
    @5
    @1
    @0
    @33
    @2
    cP
    cR
    pmatcollpw.p
    ply1assa
    3ad2ant2
    adantr
    3ad2ant1
    @11
    @36
    @13
    cR
    cbs
    cfv
    #
    wcel
    #
    @11
    cN
    cR
    cmat
    co
    #
    @41
    cbs
    cfv
    #
    cR
    @7
    @9
    @39
    @12
    cN
    @41
    eqid
    #
    @39
    eqid
    #
    @42
    eqid
    #
    @6
    @8
    @10
    simp2
    #
    @6
    @8
    @10
    simp3
    #
    @6
    @8
    @12
    @42
    wcel
    #
    @10
    @6
    @1
    @2
    @5
    @48
    @3
    @1
    @5
    @0
    @1
    @2
    simp2
    adantr
    #
    @3
    @2
    @5
    @0
    @1
    @2
    simp3
    adantr
    @3
    @5
    simpr
    @41
    cB
    cC
    @42
    cP
    cR
    @4
    cM
    cN
    ccrg
    pmatcollpw.p
    pmatcollpw.c
    pmatcollpw.b
    @43
    @45
    decpmatcl
    syl3anc
    #
    3ad2ant1
    matecld
    @6
    @8
    @36
    @40
    wb
    #
    @10
    @3
    @51
    @5
    @3
    @35
    @39
    @13
    @3
    @34
    cR
    cbs
    @3
    cR
    @34
    @3
    cR
    crg
    wcel
    #
    cR
    @34
    wceq
    @1
    @0
    @52
    @2
    cR
    crngring
    #
    3ad2ant2
    #
    cP
    cR
    crg
    pmatcollpw.p
    ply1sca
    syl
    eqcomd
    fveq2d
    eleq2d
    adantr
    3ad2ant1
    mpbird
    @6
    @8
    @38
    @10
    @3
    @52
    @5
    @38
    @54
    @37
    @4
    cP
    cR
    c.ex
    cP
    cmgp
    cfv
    #
    cX
    pmatcollpw.p
    pmatcollpw.x
    @55
    eqid
    pmatcollpw.e
    @37
    eqid
    #
    ply1moncl
    sylan
    #
    3ad2ant1
    @20
    @13
    @15
    @24
    @34
    @35
    @37
    cP
    @14
    @20
    eqid
    #
    @34
    eqid
    @35
    eqid
    @56
    @24
    eqid
    #
    @15
    eqid
    asclmul2
    syl3anc
    @11
    @31
    @23
    @14
    @24
    @11
    @23
    @31
    @11
    vi
    vj
    @7
    @9
    cN
    cN
    @21
    @31
    @22
    cvv
    @11
    @22
    eqidd
    @17
    @7
    wceq
    @18
    @9
    wceq
    wa
    #
    @21
    @31
    wceq
    @11
    @60
    @19
    @13
    @20
    @17
    @7
    @18
    @9
    @12
    oveq12
    fveq2d
    adantl
    @46
    @47
    @11
    @13
    @20
    fvexd
    ovmpt2d
    eqcomd
    oveq2d
    eqtr3d
    @11
    cP
    crg
    wcel
    #
    @38
    @22
    cB
    wcel
    #
    wa
    #
    @8
    @10
    wa
    @27
    @25
    wceq
    @6
    @8
    @61
    @10
    @3
    @61
    @5
    @1
    @0
    @61
    @2
    @1
    @52
    @61
    @53
    cP
    cR
    pmatcollpw.p
    ply1ring
    syl
    3ad2ant2
    adantr
    #
    3ad2ant1
    @6
    @8
    @63
    @10
    @6
    @38
    @62
    @57
    @6
    vi
    vj
    cC
    cB
    @21
    cP
    @37
    cN
    crg
    pmatcollpw.c
    @56
    pmatcollpw.b
    @0
    @1
    @2
    @5
    simpl1
    #
    @64
    @6
    @17
    cN
    wcel
    #
    @18
    cN
    wcel
    #
    w3a
    #
    @52
    @19
    @39
    wcel
    @21
    @37
    wcel
    @6
    @66
    @52
    @67
    @6
    @1
    @52
    @49
    @53
    syl
    3ad2ant1
    @68
    @41
    @42
    cR
    @17
    @18
    @39
    @12
    cN
    @43
    @44
    @45
    @6
    @66
    @67
    simp2
    @6
    @66
    @67
    simp3
    @6
    @66
    @48
    @67
    @50
    3ad2ant1
    matecld
    @20
    @37
    cP
    cR
    @19
    @39
    pmatcollpw.p
    @58
    @44
    @56
    ply1sclcl
    syl2anc
    matbas2d
    jca
    3ad2ant1
    @11
    @8
    @10
    @46
    @47
    jca
    cC
    cB
    cP
    c.as
    @24
    @7
    @9
    @37
    cN
    @14
    @22
    pmatcollpw.c
    pmatcollpw.b
    @56
    pmatcollpw.m
    @59
    matvscacell
    syl3anc
    @6
    @8
    @27
    @30
    wceq
    @10
    @6
    @26
    @29
    @7
    @9
    @6
    @22
    @28
    @14
    c.as
    @6
    @28
    @22
    @6
    @0
    @52
    @48
    @28
    @22
    wceq
    @65
    @3
    @52
    @5
    @54
    adantr
    @50
    vi
    vj
    @41
    @42
    cP
    cR
    @20
    cT
    @12
    cN
    crg
    pmatcollpw.t
    @43
    @45
    pmatcollpw.p
    @58
    mat2pmatval
    syl3anc
    eqcomd
    oveq2d
    oveqd
    3ad2ant1
    3eqtr2d
end
