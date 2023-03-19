include "ccrg.mm"
include "wcel.mm"
include "cid.mm"
include "cres.mm"
include "wceq.mm"
include "w3a.mm"
include "ccom.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "fveq2.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "3ad2ant3.mm"
include "wa.mm"
include "cur.mm"
include "cfn.mm"
include "cvv.mm"
include "matrcl.mm"
include "simpld.mm"
include "csymg.mm"
include "c0g.mm"
include "czrh.mm"
include "cpsgn.mm"
include "coeq12i.mm"
include "a1i.mm"
include "eqid.mm"
include "symgid.mm"
include "adantl.mm"
include "fveq12d.mm"
include "cmhm.mm"
include "crg.mm"
include "crngring.mm"
include "cmgp.mm"
include "zrhpsgnmhm.mm"
include "oveq2i.mm"
include "syl6eleqr.mm"
include "sylan.mm"
include "ringidval.mm"
include "mhm0.mm"
include "syl.mm"
include "eqtrd.mm"
include "fvresi.mm"
include "mpteq2dva.mm"
include "sylan2.mm"
include "cbs.mm"
include "adantr.mm"
include "matgsumcl.mm"
include "ringlidm.mm"
include "syl2anc.mm"
include "3adant3.mm"

theorem madetsumid
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let cM: class M
  let cN: class N
  let cY: class Y
  let vr: setvar r
  assume madetsumid.a: |- A = ( N Mat R )
  assume madetsumid.b: |- B = ( Base ` A )
  assume madetsumid.u: |- U = ( mulGrp ` R )
  assume madetsumid.y: |- Y = ( ZRHom ` R )
  assume madetsumid.s: |- S = ( pmSgn ` N )
  assume madetsumid.t: |- .x. = ( .r ` R )

  disjoint B r
  disjoint M r
  disjoint N r
  disjoint R r
  disjoint P r
  assert |- ( ( R e. CRing /\ M e. B /\ P = ( _I |` N ) ) -> ( ( ( Y o. S ) ` P ) .x. ( U gsum ( r e. N |-> ( ( P ` r ) M r ) ) ) ) = ( U gsum ( r e. N |-> ( r M r ) ) ) )

  proof
    cR
    ccrg
    wcel
    #
    cM
    cB
    wcel
    #
    cP
    cid
    cN
    cres
    #
    wceq
    #
    w3a
    cP
    cY
    cS
    ccom
    #
    cfv
    #
    cU
    vr
    cN
    vr
    cv
    #
    cP
    cfv
    #
    @6
    cM
    co
    #
    cmpt
    #
    cgsu
    co
    #
    c.x
    co
    #
    @2
    @4
    cfv
    #
    cU
    vr
    cN
    @6
    @2
    cfv
    #
    @6
    cM
    co
    #
    cmpt
    #
    cgsu
    co
    #
    c.x
    co
    #
    cU
    vr
    cN
    @6
    @6
    cM
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @3
    @0
    @11
    @17
    wceq
    @1
    @3
    @5
    @12
    @10
    @16
    c.x
    cP
    @2
    @4
    fveq2
    @3
    @9
    @15
    cU
    cgsu
    @3
    vr
    cN
    @8
    @14
    @3
    @7
    @13
    @6
    cM
    @6
    cP
    @2
    fveq1
    oveq1d
    mpteq2dv
    oveq2d
    oveq12d
    3ad2ant3
    @0
    @1
    @17
    @20
    wceq
    @3
    @0
    @1
    wa
    #
    @17
    cR
    cur
    cfv
    #
    @20
    c.x
    co
    #
    @20
    @1
    @0
    cN
    cfn
    wcel
    #
    @17
    @23
    wceq
    @1
    @24
    cR
    cvv
    wcel
    cA
    cB
    cR
    cN
    cM
    madetsumid.a
    madetsumid.b
    matrcl
    simpld
    @0
    @24
    wa
    #
    @12
    @22
    @16
    @20
    c.x
    @25
    @12
    cN
    csymg
    cfv
    #
    c0g
    cfv
    #
    cR
    czrh
    cfv
    #
    cN
    cpsgn
    cfv
    #
    ccom
    #
    cfv
    #
    @22
    @25
    @2
    @27
    @4
    @30
    @4
    @30
    wceq
    @25
    cY
    @28
    cS
    @29
    madetsumid.y
    madetsumid.s
    coeq12i
    a1i
    @24
    @2
    @27
    wceq
    @0
    cN
    @26
    cfn
    @26
    eqid
    symgid
    adantl
    fveq12d
    @25
    @30
    @26
    cU
    cmhm
    co
    #
    wcel
    #
    @31
    @22
    wceq
    @0
    cR
    crg
    wcel
    #
    @24
    @33
    cR
    crngring
    #
    @34
    @24
    wa
    @30
    @26
    cR
    cmgp
    cfv
    #
    cmhm
    co
    @32
    cN
    cR
    zrhpsgnmhm
    cU
    @36
    @26
    cmhm
    madetsumid.u
    oveq2i
    syl6eleqr
    sylan
    @26
    cU
    @30
    @22
    @27
    @27
    eqid
    cR
    @22
    cU
    madetsumid.u
    @22
    eqid
    #
    ringidval
    mhm0
    syl
    eqtrd
    @25
    @15
    @19
    cU
    cgsu
    @25
    vr
    cN
    @14
    @18
    @25
    @6
    cN
    wcel
    #
    wa
    @13
    @6
    @6
    cM
    @38
    @13
    @6
    wceq
    @25
    cN
    @6
    fvresi
    adantl
    oveq1d
    mpteq2dva
    oveq2d
    oveq12d
    sylan2
    @21
    @34
    @20
    cR
    cbs
    cfv
    #
    wcel
    @23
    @20
    wceq
    @0
    @34
    @1
    @35
    adantr
    cA
    cB
    cR
    cU
    cM
    cN
    vr
    madetsumid.a
    madetsumid.b
    madetsumid.u
    matgsumcl
    @39
    cR
    c.x
    @22
    @20
    @39
    eqid
    madetsumid.t
    @37
    ringlidm
    syl2anc
    eqtrd
    3adant3
    eqtrd
end
