include "crg.mm"
include "wcel.mm"
include "cfn.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "co.mm"
include "cmpt2.mm"
include "weq.mm"
include "cur.mm"
include "cfv.mm"
include "c0g.mm"
include "cif.mm"
include "csubma.mm"
include "cmat.mm"
include "w3a.mm"
include "cmatrepV.mm"
include "wceq.mm"
include "oveqi.mm"
include "a1i.mm"
include "cbs.mm"
include "eqid.mm"
include "mat1bas.mm"
include "adantr.mm"
include "simprr.mm"
include "simprl.mm"
include "3jca.mm"
include "3ad2ant1.mm"
include "eldifi.mm"
include "anim12i.mm"
include "3adant1.mm"
include "marepveval.mm"
include "syl2anc.mm"
include "wn.mm"
include "eldifsni.mm"
include "neneqd.mm"
include "3ad2ant3.mm"
include "iffalsed.mm"
include "simp1lr.mm"
include "simp1ll.mm"
include "3ad2ant2.mm"
include "mat1ov.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "mpt2eq3dva.mm"
include "ma1repvcl.mm"
include "ancom2s.mm"
include "syl5eqel.mm"
include "submaval.mm"
include "syl3anc.mm"
include "diffi.mm"
include "anim2i.mm"
include "ancomd.mm"
include "mat1.mm"
include "syl.mm"
include "3eqtr4d.mm"

theorem 1marepvsma1
  let cR: class R
  let c.1: class .1.
  let cI: class I
  let cN: class N
  let cV: class V
  let cX: class X
  let cZ: class Z
  let vi: setvar i
  let vj: setvar j
  assume 1marepvsma1.v: |- V = ( ( Base ` R ) ^m N )
  assume 1marepvsma1.1: |- .1. = ( 1r ` ( N Mat R ) )
  assume 1marepvsma1.x: |- X = ( ( .1. ( N matRepV R ) Z ) ` I )


  assert |- ( ( ( R e. Ring /\ N e. Fin ) /\ ( I e. N /\ Z e. V ) ) -> ( I ( ( N subMat R ) ` X ) I ) = ( 1r ` ( ( N \ { I } ) Mat R ) ) )

  proof
    cR
    crg
    wcel
    #
    cN
    cfn
    wcel
    #
    wa
    #
    cI
    cN
    wcel
    #
    cZ
    cV
    wcel
    #
    wa
    #
    wa
    #
    vi
    vj
    cN
    cI
    csn
    #
    cdif
    #
    @8
    vi
    cv
    #
    vj
    cv
    #
    cX
    co
    #
    cmpt2
    #
    vi
    vj
    @8
    @8
    vi
    vj
    weq
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
    cI
    cI
    cX
    cN
    cR
    csubma
    co
    #
    cfv
    co
    #
    @8
    cR
    cmat
    co
    #
    cur
    cfv
    #
    @6
    vi
    vj
    @8
    @8
    @11
    @15
    @6
    @9
    @8
    wcel
    #
    @10
    @8
    wcel
    #
    w3a
    #
    @11
    @9
    @10
    cI
    c.1
    cZ
    cN
    cR
    cmatrepV
    co
    #
    co
    cfv
    #
    co
    #
    @10
    cI
    wceq
    #
    @9
    cZ
    cfv
    #
    @9
    @10
    c.1
    co
    #
    cif
    #
    @15
    @11
    @26
    wceq
    @23
    cX
    @25
    @9
    @10
    1marepvsma1.x
    oveqi
    a1i
    @23
    c.1
    cN
    cR
    cmat
    co
    #
    cbs
    cfv
    #
    wcel
    #
    @4
    @3
    w3a
    #
    @9
    cN
    wcel
    #
    @10
    cN
    wcel
    #
    wa
    #
    @26
    @30
    wceq
    @6
    @21
    @34
    @22
    @6
    @33
    @4
    @3
    @2
    @33
    @5
    @31
    @32
    cR
    c.1
    cN
    @31
    eqid
    #
    @32
    eqid
    #
    1marepvsma1.1
    mat1bas
    adantr
    @2
    @3
    @4
    simprr
    @2
    @3
    @4
    simprl
    #
    3jca
    3ad2ant1
    @21
    @22
    @37
    @6
    @21
    @35
    @22
    @36
    @9
    cN
    @7
    eldifi
    #
    @10
    cN
    @7
    eldifi
    #
    anim12i
    3adant1
    @31
    @32
    cZ
    @24
    cR
    @9
    @10
    cI
    c.1
    cN
    cV
    @38
    @39
    @24
    eqid
    1marepvsma1.v
    marepveval
    syl2anc
    @23
    @30
    @29
    @15
    @23
    @27
    @28
    @29
    @22
    @6
    @27
    wn
    @21
    @22
    @10
    cI
    @10
    cN
    cI
    eldifsni
    neneqd
    3ad2ant3
    iffalsed
    @23
    @31
    cR
    c.1
    @13
    @9
    @10
    cN
    @14
    @38
    @13
    eqid
    #
    @14
    eqid
    #
    @0
    @1
    @5
    @21
    @22
    simp1lr
    @0
    @1
    @5
    @21
    @22
    simp1ll
    @21
    @6
    @35
    @22
    @41
    3ad2ant2
    @22
    @6
    @36
    @21
    @42
    3ad2ant3
    1marepvsma1.1
    mat1ov
    eqtrd
    3eqtrd
    mpt2eq3dva
    @6
    cX
    @32
    wcel
    @3
    @3
    @18
    @12
    wceq
    @6
    cX
    @25
    @32
    1marepvsma1.x
    @2
    @4
    @3
    @25
    @32
    wcel
    @31
    @32
    cZ
    cR
    c.1
    cI
    cN
    cV
    @38
    @39
    1marepvsma1.v
    1marepvsma1.1
    ma1repvcl
    ancom2s
    syl5eqel
    @40
    @40
    @31
    @32
    @17
    cR
    vi
    vj
    cI
    cI
    cX
    cN
    @38
    @17
    eqid
    @39
    submaval
    syl3anc
    @6
    @8
    cfn
    wcel
    #
    @0
    wa
    #
    @20
    @16
    wceq
    @2
    @46
    @5
    @2
    @0
    @45
    @1
    @45
    @0
    cN
    @7
    diffi
    anim2i
    ancomd
    adantr
    @19
    cR
    @13
    vi
    vj
    @8
    @14
    @19
    eqid
    @43
    @44
    mat1
    syl
    3eqtr4d
end
