include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cv.mm"
include "cn.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cmap.mm"
include "wa.mm"
include "cn0.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "c1.mm"
include "cmin.mm"
include "caddc.mm"
include "chfacfpmmulgsum.mm"
include "cbs.mm"
include "eqid.mm"
include "crg.mm"
include "crngring.mm"
include "anim2i.mm"
include "pmatring.mm"
include "syl.mm"
include "3adant3.mm"
include "ad2antrr.mm"
include "cmgp.mm"
include "cmgm.mm"
include "cmnd.mm"
include "ringmgp.mm"
include "mndmgm.mm"
include "elfznn.mm"
include "adantl.mm"
include "mat2pmatbas.mm"
include "syl3an2.mm"
include "mgpbas.mm"
include "mulgnncl.mm"
include "syl3anc.mm"
include "wf.mm"
include "elmapi.mm"
include "adantr.mm"
include "wi.mm"
include "cle.mm"
include "wbr.mm"
include "1nn0.mm"
include "a1i.mm"
include "nnnn0.mm"
include "nnge1.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "simpr.mm"
include "fz0fzdiffz0.mm"
include "syl2anc.mm"
include "ex.mm"
include "imp.mm"
include "ffvelrnd.mm"
include "df-3an.mm"
include "sylanbrc.mm"
include "simpl1.mm"
include "3ad2ant2.mm"
include "3jca.mm"
include "cuz.mm"
include "wss.mm"
include "1eluzge0.mm"
include "fzss1.mm"
include "ax-mp.mm"
include "sseli.mm"
include "anim12i.mm"
include "m2pmfzmap.mm"
include "ringcl.mm"
include "ringsubdi.mm"
include "wceq.mm"
include "ringass.mm"
include "syl13anc.mm"
include "eqcomd.mm"
include "cplusg.mm"
include "syl6eleq.mm"
include "mulgnnp1.mm"
include "syl2anr.mm"
include "mgpplusg.mm"
include "eqcomi.mm"
include "oveqd.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "mpteq2dva.mm"

theorem chfacfpmmulgsum2
  let cA: class A
  let cB: class B
  let cP: class P
  let c.pl: class .+
  let cR: class R
  let cT: class T
  let c.xp: class .X.
  let vi: setvar i
  let vn: setvar n
  let c.ex: class .^
  let cG: class G
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cY: class Y
  let c.0: class .0.
  let vs: setvar s
  let vb: setvar b
  let cK: class K
  let vk: setvar k
  let vx: setvar x
  assume cayhamlem1.a: |- A = ( N Mat R )
  assume cayhamlem1.b: |- B = ( Base ` A )
  assume cayhamlem1.p: |- P = ( Poly1 ` R )
  assume cayhamlem1.y: |- Y = ( N Mat P )
  assume cayhamlem1.r: |- .X. = ( .r ` Y )
  assume cayhamlem1.s: |- .- = ( -g ` Y )
  assume cayhamlem1.0: |- .0. = ( 0g ` Y )
  assume cayhamlem1.t: |- T = ( N matToPolyMat R )
  assume cayhamlem1.g: |- G = ( n e. NN0 |-> if ( n = 0 , ( .0. .- ( ( T ` M ) .X. ( T ` ( b ` 0 ) ) ) ) , if ( n = ( s + 1 ) , ( T ` ( b ` s ) ) , if ( ( s + 1 ) < n , .0. , ( ( T ` ( b ` ( n - 1 ) ) ) .- ( ( T ` M ) .X. ( T ` ( b ` n ) ) ) ) ) ) ) )
  assume cayhamlem1.e: |- .^ = ( .g ` ( mulGrp ` Y ) )
  assume chfacfpmmulgsum.p: |- .+ = ( +g ` Y )

  disjoint B n
  disjoint M n
  disjoint N n
  disjoint R n
  disjoint Y n
  disjoint b n
  disjoint n s
  disjoint .0. n
  disjoint B i
  disjoint G i
  disjoint M i
  disjoint N i
  disjoint R i
  disjoint T i
  disjoint .X. i
  disjoint .^ i
  disjoint i s
  disjoint b i
  disjoint T n
  disjoint i n
  disjoint Y i
  disjoint .X. n
  disjoint .- n
  disjoint K n
  disjoint B k
  disjoint B x
  disjoint i k
  disjoint i x
  disjoint k x
  disjoint G k
  disjoint G x
  disjoint M k
  disjoint M x
  disjoint N k
  disjoint N x
  disjoint R k
  disjoint R x
  disjoint T k
  disjoint T x
  disjoint .X. k
  disjoint .X. x
  disjoint .^ k
  disjoint .^ x
  disjoint .0. k
  disjoint .0. x
  disjoint k s
  disjoint s x
  disjoint b k
  disjoint b x
  disjoint k n
  assert |- ( ( ( N e. Fin /\ R e. CRing /\ M e. B ) /\ ( s e. NN /\ b e. ( B ^m ( 0 ... s ) ) ) ) -> ( Y gsum ( i e. NN0 |-> ( ( i .^ ( T ` M ) ) .X. ( G ` i ) ) ) ) = ( ( Y gsum ( i e. ( 1 ... s ) |-> ( ( ( i .^ ( T ` M ) ) .X. ( T ` ( b ` ( i - 1 ) ) ) ) .- ( ( ( i + 1 ) .^ ( T ` M ) ) .X. ( T ` ( b ` i ) ) ) ) ) ) .+ ( ( ( ( s + 1 ) .^ ( T ` M ) ) .X. ( T ` ( b ` s ) ) ) .- ( ( T ` M ) .X. ( T ` ( b ` 0 ) ) ) ) ) )

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
    vs
    cv
    #
    cn
    wcel
    #
    vb
    cv
    #
    cB
    cc0
    @4
    cfz
    co
    #
    cmap
    co
    wcel
    #
    wa
    #
    wa
    #
    cY
    vi
    cn0
    vi
    cv
    #
    cM
    cT
    cfv
    #
    c.ex
    co
    #
    @11
    cG
    cfv
    c.xp
    co
    cmpt
    cgsu
    co
    cY
    vi
    c1
    @4
    cfz
    co
    #
    @13
    @11
    c1
    cmin
    co
    #
    @6
    cfv
    #
    cT
    cfv
    #
    @12
    @11
    @6
    cfv
    cT
    cfv
    #
    c.xp
    co
    #
    c.mi
    co
    c.xp
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @4
    c1
    caddc
    co
    @12
    c.ex
    co
    @4
    @6
    cfv
    cT
    cfv
    c.xp
    co
    @12
    cc0
    @6
    cfv
    cT
    cfv
    c.xp
    co
    c.mi
    co
    #
    c.pl
    co
    cY
    vi
    @14
    @13
    @17
    c.xp
    co
    #
    @11
    c1
    caddc
    co
    @12
    c.ex
    co
    #
    @18
    c.xp
    co
    #
    c.mi
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @23
    c.pl
    co
    cA
    cB
    cP
    c.pl
    cR
    cT
    c.xp
    vi
    vn
    c.ex
    cG
    cM
    c.mi
    cN
    cY
    c.0
    vs
    vb
    cayhamlem1.a
    cayhamlem1.b
    cayhamlem1.p
    cayhamlem1.y
    cayhamlem1.r
    cayhamlem1.s
    cayhamlem1.0
    cayhamlem1.t
    cayhamlem1.g
    cayhamlem1.e
    chfacfpmmulgsum.p
    chfacfpmmulgsum
    @10
    @22
    @29
    @23
    c.pl
    @10
    @21
    @28
    cY
    cgsu
    @10
    vi
    @14
    @20
    @27
    @10
    @11
    @14
    wcel
    #
    wa
    #
    @20
    @24
    @13
    @19
    c.xp
    co
    #
    c.mi
    co
    @27
    @31
    cY
    cbs
    cfv
    #
    cY
    c.xp
    c.mi
    @13
    @17
    @19
    @33
    eqid
    #
    cayhamlem1.r
    cayhamlem1.s
    @3
    cY
    crg
    wcel
    #
    @9
    @30
    @0
    @1
    @35
    @2
    @0
    @1
    wa
    @0
    cR
    crg
    wcel
    #
    wa
    #
    @35
    @1
    @36
    @0
    cR
    crngring
    #
    anim2i
    #
    cY
    cP
    cR
    cN
    cayhamlem1.p
    cayhamlem1.y
    pmatring
    #
    syl
    3adant3
    #
    ad2antrr
    @31
    cY
    cmgp
    cfv
    #
    cmgm
    wcel
    #
    @11
    cn
    wcel
    #
    @12
    @33
    wcel
    #
    @13
    @33
    wcel
    #
    @3
    @43
    @9
    @30
    @3
    @35
    @43
    @41
    @35
    @42
    cmnd
    wcel
    @43
    cY
    @42
    @42
    eqid
    #
    ringmgp
    @42
    mndmgm
    syl
    syl
    ad2antrr
    @30
    @44
    @10
    @11
    @4
    elfznn
    #
    adantl
    @3
    @45
    @9
    @30
    @1
    @0
    @36
    @2
    @45
    @38
    cA
    cB
    cY
    cP
    cR
    cT
    cM
    cN
    cayhamlem1.t
    cayhamlem1.a
    cayhamlem1.b
    cayhamlem1.p
    cayhamlem1.y
    mat2pmatbas
    syl3an2
    #
    ad2antrr
    #
    @33
    c.ex
    @42
    @11
    @12
    @33
    cY
    @42
    @47
    @34
    mgpbas
    #
    cayhamlem1.e
    mulgnncl
    syl3anc
    #
    @31
    @0
    @36
    @16
    cB
    wcel
    #
    w3a
    #
    @17
    @33
    wcel
    @31
    @37
    @53
    @54
    @3
    @37
    @9
    @30
    @0
    @1
    @37
    @2
    @39
    3adant3
    #
    ad2antrr
    @31
    @7
    cB
    @15
    @6
    @10
    @7
    cB
    @6
    wf
    #
    @30
    @9
    @56
    @3
    @8
    @56
    @5
    @6
    cB
    @7
    elmapi
    adantl
    adantl
    adantr
    @10
    @30
    @15
    @7
    wcel
    #
    @9
    @30
    @57
    wi
    #
    @3
    @5
    @58
    @8
    @5
    @30
    @57
    @5
    @30
    wa
    #
    c1
    @7
    wcel
    #
    @30
    @57
    @59
    c1
    cn0
    wcel
    #
    @4
    cn0
    wcel
    #
    c1
    @4
    cle
    wbr
    #
    @60
    @61
    @59
    1nn0
    a1i
    @5
    @62
    @30
    @4
    nnnn0
    #
    adantr
    @5
    @63
    @30
    @4
    nnge1
    adantr
    c1
    @4
    elfz2nn0
    syl3anbrc
    @5
    @30
    simpr
    @11
    c1
    @4
    fz0fzdiffz0
    syl2anc
    ex
    adantr
    adantl
    imp
    ffvelrnd
    @0
    @36
    @53
    df-3an
    sylanbrc
    cA
    cB
    cY
    cP
    cR
    cT
    @16
    cN
    cayhamlem1.t
    cayhamlem1.a
    cayhamlem1.b
    cayhamlem1.p
    cayhamlem1.y
    mat2pmatbas
    syl
    @31
    @35
    @45
    @18
    @33
    wcel
    #
    @19
    @33
    wcel
    @3
    @35
    @9
    @30
    @3
    @37
    @35
    @55
    @40
    syl
    ad2antrr
    #
    @50
    @31
    @0
    @36
    @62
    w3a
    #
    @8
    @11
    @7
    wcel
    #
    wa
    @65
    @10
    @67
    @30
    @10
    @0
    @36
    @62
    @0
    @1
    @2
    @9
    simpl1
    @3
    @36
    @9
    @1
    @0
    @36
    @2
    @38
    3ad2ant2
    adantr
    @9
    @62
    @3
    @5
    @62
    @8
    @64
    adantr
    adantl
    3jca
    adantr
    @10
    @8
    @30
    @68
    @9
    @8
    @3
    @5
    @8
    simpr
    adantl
    @14
    @7
    @11
    c1
    cc0
    cuz
    cfv
    wcel
    @14
    @7
    wss
    1eluzge0
    c1
    cc0
    @4
    fzss1
    ax-mp
    sseli
    anim12i
    cA
    cB
    cP
    cR
    @4
    cT
    @11
    cN
    cY
    vb
    cayhamlem1.a
    cayhamlem1.b
    cayhamlem1.p
    cayhamlem1.y
    cayhamlem1.t
    m2pmfzmap
    syl2anc
    #
    @33
    cY
    c.xp
    @12
    @18
    @34
    cayhamlem1.r
    ringcl
    syl3anc
    ringsubdi
    @31
    @32
    @26
    @24
    c.mi
    @31
    @32
    @13
    @12
    c.xp
    co
    #
    @18
    c.xp
    co
    #
    @26
    @31
    @71
    @32
    @31
    @35
    @46
    @45
    @65
    @71
    @32
    wceq
    @66
    @52
    @50
    @69
    @33
    cY
    c.xp
    @13
    @12
    @18
    @34
    cayhamlem1.r
    ringass
    syl13anc
    eqcomd
    @31
    @70
    @25
    @18
    c.xp
    @31
    @25
    @70
    @31
    @25
    @13
    @12
    @42
    cplusg
    cfv
    #
    co
    #
    @70
    @30
    @44
    @12
    @42
    cbs
    cfv
    #
    wcel
    #
    @25
    @73
    wceq
    @10
    @48
    @3
    @75
    @9
    @3
    @12
    @33
    @74
    @49
    @51
    syl6eleq
    adantr
    @74
    @72
    c.ex
    @42
    @11
    @12
    @74
    eqid
    cayhamlem1.e
    @72
    eqid
    mulgnnp1
    syl2anr
    @31
    @72
    c.xp
    @13
    @12
    @72
    c.xp
    wceq
    @31
    c.xp
    @72
    cY
    c.xp
    @42
    @47
    cayhamlem1.r
    mgpplusg
    eqcomi
    a1i
    oveqd
    eqtrd
    eqcomd
    oveq1d
    eqtrd
    oveq2d
    eqtrd
    mpteq2dva
    oveq2d
    oveq1d
    eqtrd
end
