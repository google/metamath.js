include "chlh.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cplusg.mm"
include "csca.mm"
include "ctp.mm"
include "cvsca.mm"
include "cip.mm"
include "cpr.mm"
include "cun.mm"
include "cv.mm"
include "cdvh.mm"
include "cedring.mm"
include "cstv.mm"
include "chg.mm"
include "csts.mm"
include "co.mm"
include "chdma.mm"
include "cmpt2.mm"
include "csb.mm"
include "cvv.mm"
include "wcel.mm"
include "cmpt.mm"
include "wceq.mm"
include "chlt.mm"
include "wa.mm"
include "elex.mm"
include "adantr.mm"
include "syl.mm"
include "clh.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfmpt.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "csbeq1a.mm"
include "mpteq12dv.mm"
include "df-hlhil.mm"
include "fvmptf.mm"
include "sylancl.mm"
include "fvexd.mm"
include "id.mm"
include "simpr.mm"
include "fveq2d.mm"
include "simplr.mm"
include "fveq12d.mm"
include "sylan9eqr.mm"
include "opeq2d.mm"
include "oveq12d.mm"
include "ad2antrr.mm"
include "tpeq123d.mm"
include "fveq1d.mm"
include "mpt2eq123dv.mm"
include "preq12d.mm"
include "uneq12d.mm"
include "csbied.mm"
include "simprd.mm"
include "tpex.mm"
include "prex.mm"
include "unex.mm"
include "a1i.mm"
include "fvmptd.mm"
include "syl5eq.mm"

theorem hlhilset
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let cE: class E
  let cG: class G
  let cH: class H
  let c.xi: class .,
  let cK: class K
  let cL: class L
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vw: setvar w
  let vu: setvar u
  let vv: setvar v
  assume hlhilset.h: |- H = ( LHyp ` K )
  assume hlhilset.l: |- L = ( ( HLHil ` K ) ` W )
  assume hlhilset.u: |- U = ( ( DVecH ` K ) ` W )
  assume hlhilset.v: |- V = ( Base ` U )
  assume hlhilset.p: |- .+ = ( +g ` U )
  assume hlhilset.e: |- E = ( ( EDRing ` K ) ` W )
  assume hlhilset.g: |- G = ( ( HGMap ` K ) ` W )
  assume hlhilset.r: |- R = ( E sSet <. ( *r ` ndx ) , G >. )
  assume hlhilset.t: |- .x. = ( .s ` U )
  assume hlhilset.s: |- S = ( ( HDMap ` K ) ` W )
  assume hlhilset.i: |- ., = ( x e. V , y e. V |-> ( ( S ` y ) ` x ) )
  assume hlhilset.k: |- ( ph -> ( K e. HL /\ W e. H ) )

  disjoint x y
  disjoint K x
  disjoint K y
  disjoint ph x
  disjoint ph y
  disjoint W x
  disjoint W y
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint K k
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint K u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint K v
  disjoint w x
  disjoint w y
  disjoint K w
  disjoint k ph
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint R k
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint .+ k
  disjoint .+ u
  disjoint .+ v
  disjoint .+ w
  disjoint ., k
  disjoint ., u
  disjoint ., v
  disjoint ., w
  disjoint W k
  disjoint W u
  disjoint W v
  disjoint W w
  disjoint .x. k
  disjoint .x. u
  disjoint .x. v
  disjoint .x. w
  disjoint V k
  disjoint V u
  disjoint V v
  disjoint V w
  assert |- ( ph -> L = ( { <. ( Base ` ndx ) , V >. , <. ( +g ` ndx ) , .+ >. , <. ( Scalar ` ndx ) , R >. } u. { <. ( .s ` ndx ) , .x. >. , <. ( .i ` ndx ) , ., >. } ) )

  proof
    wph
    cL
    cW
    cK
    chlh
    cfv
    #
    cfv
    cnx
    cbs
    cfv
    #
    cV
    cop
    #
    cnx
    cplusg
    cfv
    #
    c.pl
    cop
    #
    cnx
    csca
    cfv
    #
    cR
    cop
    #
    ctp
    #
    cnx
    cvsca
    cfv
    #
    c.x
    cop
    #
    cnx
    cip
    cfv
    #
    c.xi
    cop
    #
    cpr
    #
    cun
    #
    hlhilset.l
    wph
    vw
    cW
    vk
    cK
    vu
    vw
    cv
    #
    vk
    cv
    #
    cdvh
    cfv
    #
    cfv
    #
    vv
    vu
    cv
    #
    cbs
    cfv
    #
    @1
    vv
    cv
    #
    cop
    #
    @3
    @18
    cplusg
    cfv
    #
    cop
    #
    @5
    @14
    @15
    cedring
    cfv
    #
    cfv
    #
    cnx
    cstv
    cfv
    #
    @14
    @15
    chg
    cfv
    #
    cfv
    #
    cop
    #
    csts
    co
    #
    cop
    #
    ctp
    #
    @8
    @18
    cvsca
    cfv
    #
    cop
    #
    @10
    vx
    vy
    @20
    @20
    vx
    cv
    #
    vy
    cv
    #
    @14
    @15
    chdma
    cfv
    #
    cfv
    #
    cfv
    #
    cfv
    #
    cmpt2
    #
    cop
    #
    cpr
    #
    cun
    #
    csb
    #
    csb
    #
    csb
    #
    @13
    cH
    @0
    cvv
    wph
    cK
    cvv
    wcel
    #
    vw
    cH
    @47
    cmpt
    #
    cvv
    wcel
    @0
    @49
    wceq
    wph
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    @48
    hlhilset.k
    @50
    @48
    @51
    cK
    chlt
    elex
    adantr
    syl
    #
    vw
    cH
    @47
    cH
    cK
    clh
    cfv
    #
    cvv
    hlhilset.h
    cK
    clh
    fvex
    eqeltri
    mptex
    vk
    cK
    vw
    @15
    clh
    cfv
    #
    @46
    cmpt
    @49
    cvv
    chlh
    cvv
    vk
    cK
    nfcv
    vk
    vw
    cH
    @47
    vk
    cH
    nfcv
    vk
    cK
    @46
    nfcsb1v
    nfmpt
    @15
    cK
    wceq
    #
    vw
    @54
    @46
    cH
    @47
    @55
    @54
    @53
    cH
    @15
    cK
    clh
    fveq2
    hlhilset.h
    syl6eqr
    vk
    cK
    @46
    csbeq1a
    mpteq12dv
    vx
    vy
    vw
    vv
    vu
    vk
    df-hlhil
    fvmptf
    sylancl
    wph
    @14
    cW
    wceq
    #
    wa
    #
    vk
    cK
    @46
    @13
    cvv
    wph
    @48
    @56
    @52
    adantr
    @57
    @55
    wa
    #
    vu
    @17
    @45
    @13
    cvv
    @58
    @14
    @16
    fvexd
    @58
    @18
    @17
    wceq
    #
    wa
    #
    vv
    @19
    @44
    @13
    cvv
    @60
    @18
    cbs
    fvexd
    @60
    @20
    @19
    wceq
    #
    wa
    #
    @32
    @7
    @43
    @12
    @62
    @21
    @2
    @23
    @4
    @31
    @6
    @62
    @20
    cV
    @1
    @61
    @60
    @20
    @19
    cV
    @61
    id
    @60
    @19
    cU
    cbs
    cfv
    cV
    @60
    @18
    cU
    cbs
    @59
    @58
    @18
    @17
    cU
    @59
    id
    @58
    @17
    cW
    cK
    cdvh
    cfv
    #
    cfv
    cU
    @58
    @14
    cW
    @16
    @63
    @58
    @15
    cK
    cdvh
    @57
    @55
    simpr
    #
    fveq2d
    wph
    @56
    @55
    simplr
    #
    fveq12d
    hlhilset.u
    syl6eqr
    sylan9eqr
    #
    fveq2d
    hlhilset.v
    syl6eqr
    sylan9eqr
    #
    opeq2d
    @62
    @22
    c.pl
    @3
    @62
    @22
    cU
    cplusg
    cfv
    c.pl
    @62
    @18
    cU
    cplusg
    @60
    @18
    cU
    wceq
    @61
    @66
    adantr
    #
    fveq2d
    hlhilset.p
    syl6eqr
    opeq2d
    @58
    @31
    @6
    wceq
    @59
    @61
    @58
    @30
    cR
    @5
    @58
    @30
    cE
    @26
    cG
    cop
    #
    csts
    co
    cR
    @58
    @25
    cE
    @29
    @69
    csts
    @58
    @25
    cW
    cK
    cedring
    cfv
    #
    cfv
    cE
    @58
    @14
    cW
    @24
    @70
    @58
    @15
    cK
    cedring
    @64
    fveq2d
    @65
    fveq12d
    hlhilset.e
    syl6eqr
    @58
    @28
    cG
    @26
    @58
    @28
    cW
    cK
    chg
    cfv
    #
    cfv
    cG
    @58
    @14
    cW
    @27
    @71
    @58
    @15
    cK
    chg
    @64
    fveq2d
    @65
    fveq12d
    hlhilset.g
    syl6eqr
    opeq2d
    oveq12d
    hlhilset.r
    syl6eqr
    opeq2d
    ad2antrr
    tpeq123d
    @62
    @34
    @9
    @42
    @11
    @62
    @33
    c.x
    @8
    @62
    @33
    cU
    cvsca
    cfv
    c.x
    @62
    @18
    cU
    cvsca
    @68
    fveq2d
    hlhilset.t
    syl6eqr
    opeq2d
    @62
    @41
    c.xi
    @10
    @62
    @41
    vx
    vy
    cV
    cV
    @35
    @36
    cS
    cfv
    #
    cfv
    #
    cmpt2
    c.xi
    @62
    vx
    vy
    @20
    @20
    @40
    cV
    cV
    @73
    @67
    @67
    @62
    @35
    @39
    @72
    @62
    @36
    @38
    cS
    @58
    @38
    cS
    wceq
    @59
    @61
    @58
    @38
    cW
    cK
    chdma
    cfv
    #
    cfv
    cS
    @58
    @14
    cW
    @37
    @74
    @58
    @15
    cK
    chdma
    @64
    fveq2d
    @65
    fveq12d
    hlhilset.s
    syl6eqr
    ad2antrr
    fveq1d
    fveq1d
    mpt2eq123dv
    hlhilset.i
    syl6eqr
    opeq2d
    preq12d
    uneq12d
    csbied
    csbied
    csbied
    wph
    @50
    @51
    hlhilset.k
    simprd
    @13
    cvv
    wcel
    wph
    @7
    @12
    @2
    @4
    @6
    tpex
    @9
    @11
    prex
    unex
    a1i
    fvmptd
    syl5eq
end
