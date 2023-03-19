include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "cmzp.mm"
include "cfv.mm"
include "wa.mm"
include "cv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cres.mm"
include "wceq.mm"
include "cc0.mm"
include "cmap.mm"
include "wrex.mm"
include "cab.mm"
include "cdioph.mm"
include "simpl.mm"
include "simpr.mm"
include "eqidd.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "abbidv.mm"
include "weq.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "reseq1.mm"
include "eqeq2d.mm"
include "fveq2.mm"
include "anbi12d.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "cbvabv.mm"
include "syl6eq.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "eldioph3b.mm"
include "sylanbrc.mm"

theorem eldioph3
  let vu: setvar u
  let vt: setvar t
  let cP: class P
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vp: setvar p

  disjoint N t
  disjoint N u
  disjoint t u
  disjoint P t
  disjoint P u
  disjoint N a
  disjoint N b
  disjoint N p
  disjoint a b
  disjoint a p
  disjoint a t
  disjoint a u
  disjoint b p
  disjoint b t
  disjoint b u
  disjoint p t
  disjoint p u
  disjoint P a
  disjoint P b
  disjoint P p
  assert |- ( ( N e. NN0 /\ P e. ( mzPoly ` NN ) ) -> { t | E. u e. ( NN0 ^m NN ) ( t = ( u |` ( 1 ... N ) ) /\ ( P ` u ) = 0 ) } e. ( Dioph ` N ) )

  proof
    cN
    cn0
    wcel
    #
    cP
    cn
    cmzp
    cfv
    #
    wcel
    #
    wa
    #
    @0
    vt
    cv
    #
    vu
    cv
    #
    c1
    cN
    cfz
    co
    #
    cres
    #
    wceq
    #
    @5
    cP
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vu
    cn0
    cn
    cmap
    co
    #
    wrex
    #
    vt
    cab
    #
    va
    cv
    #
    vb
    cv
    #
    @6
    cres
    #
    wceq
    #
    @16
    vp
    cv
    #
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vb
    @12
    wrex
    #
    va
    cab
    #
    wceq
    #
    vp
    @1
    wrex
    #
    @14
    cN
    cdioph
    cfv
    wcel
    @0
    @2
    simpl
    @3
    @2
    @14
    @14
    wceq
    #
    @26
    @0
    @2
    simpr
    @3
    @14
    eqidd
    @25
    @27
    vp
    cP
    @1
    @19
    cP
    wceq
    #
    @24
    @14
    @14
    @28
    @24
    @18
    @16
    cP
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vb
    @12
    wrex
    #
    va
    cab
    @14
    @28
    @23
    @32
    va
    @28
    @22
    @31
    vb
    @12
    @28
    @21
    @30
    @18
    @28
    @20
    @29
    cc0
    @16
    @19
    cP
    fveq1
    eqeq1d
    anbi2d
    rexbidv
    abbidv
    @32
    @13
    va
    vt
    va
    vt
    weq
    #
    @32
    @4
    @17
    wceq
    #
    @30
    wa
    #
    vb
    @12
    wrex
    @13
    @33
    @31
    @35
    vb
    @12
    @33
    @18
    @34
    @30
    @15
    @4
    @17
    eqeq1
    anbi1d
    rexbidv
    @35
    @11
    vb
    vu
    @12
    vb
    vu
    weq
    #
    @34
    @8
    @30
    @10
    @36
    @17
    @7
    @4
    @16
    @5
    @6
    reseq1
    eqeq2d
    @36
    @29
    @9
    cc0
    @16
    @5
    cP
    fveq2
    eqeq1d
    anbi12d
    cbvrexv
    syl6bb
    cbvabv
    syl6eq
    eqeq2d
    rspcev
    syl2anc
    vb
    va
    @14
    cN
    vp
    eldioph3b
    sylanbrc
end
