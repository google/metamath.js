include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "w3a.mm"
include "cmarrep.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "cxp.mm"
include "cres.mm"
include "cur.mm"
include "cminmar1.mm"
include "cv.mm"
include "wceq.mm"
include "c0g.mm"
include "cif.mm"
include "cmpt2.mm"
include "mpt2difsnif.mm"
include "eqtr4i.mm"
include "wss.mm"
include "wa.mm"
include "difss.mm"
include "ssid.mm"
include "pm3.2i.mm"
include "resmpt2.mm"
include "mp1i.mm"
include "3eqtr4a.mm"
include "simp1.mm"
include "simp3.mm"
include "simp2.mm"
include "eqid.mm"
include "marrepval.mm"
include "syl22anc.mm"
include "reseq1d.mm"
include "ccrg.mm"
include "crg.mm"
include "crngring.mm"
include "ringidcl.mm"
include "syl.mm"
include "3eqtr4d.mm"
include "ax-mp.mm"
include "minmar1marrep.mm"
include "sylancr.mm"
include "eqcomd.mm"
include "oveqd.mm"
include "eqtrd.mm"

theorem smadiadetglem1
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
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


  assert |- ( ( M e. B /\ K e. N /\ S e. ( Base ` R ) ) -> ( ( K ( M ( N matRRep R ) S ) K ) |` ( ( N \ { K } ) X. N ) ) = ( ( K ( ( N minMatR1 R ) ` M ) K ) |` ( ( N \ { K } ) X. N ) ) )

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
    cN
    cK
    csn
    #
    cdif
    #
    cN
    cxp
    #
    cres
    #
    cK
    cK
    cM
    cR
    cur
    cfv
    #
    @5
    co
    #
    co
    #
    @9
    cres
    #
    cK
    cK
    cM
    cN
    cR
    cminmar1
    co
    cfv
    #
    co
    #
    @9
    cres
    @4
    vi
    vj
    cN
    cN
    vi
    cv
    #
    cK
    wceq
    #
    vj
    cv
    #
    cK
    wceq
    #
    cS
    cR
    c0g
    cfv
    #
    cif
    #
    @17
    @19
    cM
    co
    #
    cif
    #
    cmpt2
    #
    @9
    cres
    #
    vi
    vj
    cN
    cN
    @18
    @20
    @11
    @21
    cif
    #
    @23
    cif
    #
    cmpt2
    #
    @9
    cres
    #
    @10
    @14
    @4
    vi
    vj
    @8
    cN
    @24
    cmpt2
    #
    vi
    vj
    @8
    cN
    @28
    cmpt2
    #
    @26
    @30
    @31
    vi
    vj
    @8
    cN
    @23
    cmpt2
    @32
    cN
    cN
    @22
    @23
    vi
    vj
    cK
    mpt2difsnif
    cN
    cN
    @27
    @23
    vi
    vj
    cK
    mpt2difsnif
    eqtr4i
    @8
    cN
    wss
    #
    cN
    cN
    wss
    #
    wa
    #
    @26
    @31
    wceq
    @4
    @33
    @34
    cN
    @7
    difss
    cN
    ssid
    pm3.2i
    #
    vi
    vj
    cN
    cN
    @8
    cN
    @24
    resmpt2
    mp1i
    @35
    @30
    @32
    wceq
    @4
    @36
    vi
    vj
    cN
    cN
    @8
    cN
    @28
    resmpt2
    mp1i
    3eqtr4a
    @4
    @6
    @25
    @9
    @4
    @0
    @3
    @1
    @1
    @6
    @25
    wceq
    @0
    @1
    @3
    simp1
    #
    @0
    @1
    @3
    simp3
    @0
    @1
    @3
    simp2
    #
    @38
    cA
    cB
    @5
    cR
    cS
    vi
    vj
    cK
    cK
    cM
    cN
    @21
    smadiadet.a
    smadiadet.b
    @5
    eqid
    #
    @21
    eqid
    #
    marrepval
    syl22anc
    reseq1d
    @4
    @13
    @29
    @9
    @4
    @0
    @11
    @2
    wcel
    #
    @1
    @1
    @13
    @29
    wceq
    @37
    cR
    ccrg
    wcel
    #
    @41
    @4
    smadiadet.r
    @42
    cR
    crg
    wcel
    #
    @41
    cR
    crngring
    #
    @2
    cR
    @11
    @2
    eqid
    @11
    eqid
    #
    ringidcl
    syl
    mp1i
    @38
    @38
    cA
    cB
    @5
    cR
    @11
    vi
    vj
    cK
    cK
    cM
    cN
    @21
    smadiadet.a
    smadiadet.b
    @39
    @40
    marrepval
    syl22anc
    reseq1d
    3eqtr4d
    @4
    @13
    @16
    @9
    @4
    @12
    @15
    cK
    cK
    @4
    @15
    @12
    @4
    @43
    @0
    @15
    @12
    wceq
    @42
    @43
    smadiadet.r
    @44
    ax-mp
    @37
    cA
    cB
    @5
    cR
    @11
    cM
    cN
    smadiadet.a
    smadiadet.b
    @39
    @45
    minmar1marrep
    sylancr
    eqcomd
    oveqd
    reseq1d
    eqtrd
end
