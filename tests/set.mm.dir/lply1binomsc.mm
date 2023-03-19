include "ccrg.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "cbc.mm"
include "cmin.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cbs.mm"
include "wceq.mm"
include "wf.mm"
include "csca.mm"
include "eqid.mm"
include "crg.mm"
include "crngring.mm"
include "ply1ring.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "clmod.mm"
include "ply1lmod.mm"
include "asclf.mm"
include "ply1sca.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "feq2d.mm"
include "mpbird.mm"
include "simp3.mm"
include "ffvelrnd.mm"
include "lply1binom.mm"
include "syld3an3.mm"
include "wa.mm"
include "cur.mm"
include "cvsca.mm"
include "cmgp.mm"
include "cmg.mm"
include "casa.mm"
include "ply1assa.mm"
include "adantr.mm"
include "fznn0sub.mm"
include "adantl.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "3adant2.mm"
include "ringidcl.mm"
include "assamulgscm.mm"
include "syl13anc.mm"
include "eqcomd.mm"
include "oveqd.mm"
include "cmnd.mm"
include "ringmgp.mm"
include "mgpbas.mm"
include "ringidval.mm"
include "mulgnn0z.mm"
include "syl2an.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "asclval.mm"
include "oveq2d.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "syl6eq.mm"
include "eleqtrrd.mm"
include "3eqtr4d.mm"
include "oveq1d.mm"
include "mpteq2dva.mm"

theorem lply1binomsc
  let cA: class A
  let cP: class P
  let c.pl: class .+
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let vk: setvar k
  let cE: class E
  let c.ex: class .^
  let cG: class G
  let cH: class H
  let cK: class K
  let cN: class N
  let cX: class X
  assume cply1binom.p: |- P = ( Poly1 ` R )
  assume cply1binom.x: |- X = ( var1 ` R )
  assume cply1binom.a: |- .+ = ( +g ` P )
  assume cply1binom.m: |- .X. = ( .r ` P )
  assume cply1binom.t: |- .x. = ( .g ` P )
  assume cply1binom.g: |- G = ( mulGrp ` P )
  assume cply1binom.e: |- .^ = ( .g ` G )
  assume lply1binomsc.k: |- K = ( Base ` R )
  assume lply1binomsc.s: |- S = ( algSc ` P )
  assume lply1binomsc.h: |- H = ( mulGrp ` R )
  assume lply1binomsc.e: |- E = ( .g ` H )

  disjoint A k
  disjoint K k
  disjoint N k
  disjoint P k
  disjoint R k
  disjoint X k
  disjoint .X. k
  disjoint .x. k
  disjoint .^ k
  disjoint .+ k
  disjoint S k
  assert |- ( ( R e. CRing /\ N e. NN0 /\ A e. K ) -> ( N .^ ( X .+ ( S ` A ) ) ) = ( P gsum ( k e. ( 0 ... N ) |-> ( ( N _C k ) .x. ( ( S ` ( ( N - k ) E A ) ) .X. ( k .^ X ) ) ) ) ) )

  proof
    cR
    ccrg
    wcel
    #
    cN
    cn0
    wcel
    #
    cA
    cK
    wcel
    #
    w3a
    #
    cN
    cX
    cA
    cS
    cfv
    #
    c.pl
    co
    c.ex
    co
    #
    cP
    vk
    cc0
    cN
    cfz
    co
    #
    cN
    vk
    cv
    #
    cbc
    co
    #
    cN
    @7
    cmin
    co
    #
    @4
    c.ex
    co
    #
    @7
    cX
    c.ex
    co
    #
    c.xp
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cP
    vk
    @6
    @8
    @9
    cA
    cE
    co
    #
    cS
    cfv
    #
    @11
    c.xp
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    @0
    @1
    @2
    @4
    cP
    cbs
    cfv
    #
    wcel
    @5
    @15
    wceq
    @3
    cK
    @21
    cA
    cS
    @3
    cK
    @21
    cS
    wf
    cP
    csca
    cfv
    #
    cbs
    cfv
    #
    @21
    cS
    wf
    @3
    cS
    @21
    @22
    @23
    cP
    lply1binomsc.s
    @22
    eqid
    #
    @0
    @1
    cP
    crg
    wcel
    #
    @2
    @0
    cR
    crg
    wcel
    #
    @25
    cR
    crngring
    #
    cP
    cR
    cply1binom.p
    ply1ring
    syl
    #
    3ad2ant1
    @0
    @1
    cP
    clmod
    wcel
    #
    @2
    @0
    @26
    @29
    @27
    cP
    cR
    cply1binom.p
    ply1lmod
    syl
    3ad2ant1
    @23
    eqid
    #
    @21
    eqid
    #
    asclf
    @3
    cK
    @23
    @21
    cS
    @3
    cK
    cR
    cbs
    cfv
    #
    @23
    lply1binomsc.k
    @3
    cR
    @22
    cbs
    @0
    @1
    cR
    @22
    wceq
    #
    @2
    cP
    cR
    ccrg
    cply1binom.p
    ply1sca
    #
    3ad2ant1
    #
    fveq2d
    syl5eq
    feq2d
    mpbird
    @0
    @1
    @2
    simp3
    ffvelrnd
    @4
    @21
    cP
    c.pl
    cR
    c.x
    c.xp
    vk
    c.ex
    cG
    cN
    cX
    cply1binom.p
    cply1binom.x
    cply1binom.a
    cply1binom.m
    cply1binom.t
    cply1binom.g
    cply1binom.e
    @31
    lply1binom
    syld3an3
    @3
    @14
    @20
    cP
    cgsu
    @3
    vk
    @6
    @13
    @19
    @3
    @7
    @6
    wcel
    #
    wa
    #
    @12
    @18
    @8
    c.x
    @37
    @10
    @17
    @11
    c.xp
    @37
    @9
    cA
    cP
    cur
    cfv
    #
    cP
    cvsca
    cfv
    #
    co
    #
    c.ex
    co
    #
    @16
    @38
    @39
    co
    #
    @10
    @17
    @37
    @41
    @9
    cA
    @22
    cmgp
    cfv
    #
    cmg
    cfv
    #
    co
    #
    @9
    @38
    c.ex
    co
    #
    @39
    co
    #
    @42
    @37
    cP
    casa
    wcel
    #
    @9
    cn0
    wcel
    #
    cA
    @23
    wcel
    #
    @38
    @21
    wcel
    #
    @41
    @47
    wceq
    @3
    @48
    @36
    @0
    @1
    @48
    @2
    cP
    cR
    cply1binom.p
    ply1assa
    3ad2ant1
    adantr
    @36
    @49
    @3
    @7
    cc0
    cN
    fznn0sub
    #
    adantl
    #
    @3
    @50
    @36
    @0
    @2
    @50
    @1
    @0
    @2
    @50
    @0
    cK
    @23
    cA
    @0
    cK
    @32
    @23
    lply1binomsc.k
    @0
    cR
    @22
    cbs
    @34
    fveq2d
    syl5eq
    eleq2d
    biimpa
    3adant2
    adantr
    #
    @3
    @51
    @36
    @0
    @1
    @51
    @2
    @0
    @25
    @51
    @28
    @21
    cP
    @38
    @31
    @38
    eqid
    #
    ringidcl
    syl
    3ad2ant1
    adantr
    cA
    @23
    @39
    c.ex
    @44
    @22
    @43
    cG
    @9
    @21
    cP
    @38
    @31
    @24
    @30
    @39
    eqid
    #
    @43
    eqid
    @44
    eqid
    cply1binom.g
    cply1binom.e
    assamulgscm
    syl13anc
    @37
    @45
    @16
    @46
    @38
    @39
    @37
    @44
    cE
    @9
    cA
    @37
    cE
    @44
    @3
    cE
    @44
    wceq
    #
    @36
    @0
    @1
    @57
    @2
    @0
    cE
    cH
    cmg
    cfv
    @44
    lply1binomsc.e
    @0
    cH
    @43
    cmg
    @0
    cH
    cR
    cmgp
    cfv
    @43
    lply1binomsc.h
    @0
    cR
    @22
    cmgp
    @34
    fveq2d
    syl5eq
    fveq2d
    syl5eq
    3ad2ant1
    adantr
    eqcomd
    oveqd
    @3
    cG
    cmnd
    wcel
    #
    @49
    @46
    @38
    wceq
    @36
    @0
    @1
    @58
    @2
    @0
    @25
    @58
    @28
    cP
    cG
    cply1binom.g
    ringmgp
    syl
    3ad2ant1
    @52
    @21
    c.ex
    cG
    @9
    @38
    @21
    cP
    cG
    cply1binom.g
    @31
    mgpbas
    cply1binom.e
    cP
    @38
    cG
    cply1binom.g
    @55
    ringidval
    mulgnn0z
    syl2an
    oveq12d
    eqtrd
    @37
    @4
    @40
    @9
    c.ex
    @37
    @50
    @4
    @40
    wceq
    @54
    cS
    @39
    @38
    @22
    @23
    cP
    cA
    lply1binomsc.s
    @24
    @30
    @56
    @55
    asclval
    syl
    oveq2d
    @37
    @16
    @23
    wcel
    @17
    @42
    wceq
    @37
    @16
    cH
    cbs
    cfv
    #
    @23
    @37
    cH
    cmnd
    wcel
    #
    @49
    cA
    @59
    wcel
    #
    @16
    @59
    wcel
    @3
    @60
    @36
    @0
    @1
    @60
    @2
    @0
    @26
    @60
    @27
    cR
    cH
    lply1binomsc.h
    ringmgp
    syl
    3ad2ant1
    adantr
    @53
    @3
    @61
    @36
    @0
    @2
    @61
    @1
    @0
    @2
    wa
    cA
    cK
    @59
    @0
    @2
    simpr
    cK
    cR
    cH
    lply1binomsc.h
    lply1binomsc.k
    mgpbas
    syl6eleq
    3adant2
    adantr
    @59
    cE
    cH
    @9
    cA
    @59
    eqid
    lply1binomsc.e
    mulgnn0cl
    syl3anc
    @37
    @23
    @32
    @59
    @37
    @22
    cR
    cbs
    @37
    cR
    @22
    @3
    @33
    @36
    @35
    adantr
    eqcomd
    fveq2d
    @32
    cR
    cH
    lply1binomsc.h
    @32
    eqid
    mgpbas
    syl6eq
    eleqtrrd
    cS
    @39
    @38
    @22
    @23
    cP
    @16
    lply1binomsc.s
    @24
    @30
    @56
    @55
    asclval
    syl
    3eqtr4d
    oveq1d
    oveq2d
    mpteq2dva
    oveq2d
    eqtrd
end
