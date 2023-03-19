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
include "cvv.mm"
include "cfv.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "cn0.mm"
include "ovexd.mm"
include "c1.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "csb.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "nnnn0.mm"
include "ad2antrl.mm"
include "1nn0.mm"
include "nn0addcld.mm"
include "vex.mm"
include "csbov12g.mm"
include "nfcvd.mm"
include "oveq1.mm"
include "csbiegf.mm"
include "csbfv.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "mp1i.mm"
include "c2.mm"
include "cuz.mm"
include "simplll.mm"
include "simpllr.mm"
include "cz.mm"
include "cle.mm"
include "adantr.mm"
include "ad2antlr.mm"
include "nn0zd.mm"
include "2z.mm"
include "zaddcld.mm"
include "simplr.mm"
include "wb.mm"
include "peano2nn0.mm"
include "syl.mm"
include "nn0z.mm"
include "zltp1le.mm"
include "syl2an.mm"
include "biimpa.mm"
include "cc.mm"
include "nncn.mm"
include "add1p1.mm"
include "breq1d.mm"
include "bicomd.mm"
include "mpbird.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "chfacfpmmul0.mm"
include "syl3anc.mm"
include "ex.mm"
include "ralrimiva.mm"
include "breq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "mptnn0fsupp.mm"

theorem chfacfpmmulfsupp
  let cA: class A
  let cB: class B
  let cP: class P
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
  assert |- ( ( ( N e. Fin /\ R e. CRing /\ M e. B ) /\ ( s e. NN /\ b e. ( B ^m ( 0 ... s ) ) ) ) -> ( i e. NN0 |-> ( ( i .^ ( T ` M ) ) .X. ( G ` i ) ) ) finSupp .0. )

  proof
    cN
    cfn
    wcel
    cR
    ccrg
    wcel
    cM
    cB
    wcel
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
    cB
    cc0
    @1
    cfz
    co
    cmap
    co
    wcel
    #
    wa
    #
    wa
    #
    vk
    cvv
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
    @6
    cG
    cfv
    #
    c.xp
    co
    #
    vi
    cvv
    c.0
    vx
    c.0
    cvv
    wcel
    @5
    c.0
    cY
    c0g
    cfv
    cvv
    cayhamlem1.0
    cY
    c0g
    fvex
    eqeltri
    a1i
    @5
    @6
    cn0
    wcel
    wa
    @8
    @9
    c.xp
    ovexd
    @5
    @1
    c1
    caddc
    co
    #
    cn0
    wcel
    #
    @11
    vk
    cv
    #
    clt
    wbr
    #
    vi
    @13
    @10
    csb
    #
    c.0
    wceq
    #
    wi
    #
    vk
    cn0
    wral
    #
    vx
    cv
    #
    @13
    clt
    wbr
    #
    @16
    wi
    #
    vk
    cn0
    wral
    #
    vx
    cn0
    wrex
    @5
    @1
    c1
    @2
    @1
    cn0
    wcel
    #
    @0
    @3
    @1
    nnnn0
    #
    ad2antrl
    c1
    cn0
    wcel
    @5
    1nn0
    a1i
    nn0addcld
    @5
    @17
    vk
    cn0
    @5
    @13
    cn0
    wcel
    #
    wa
    #
    @14
    @16
    @26
    @14
    wa
    #
    @15
    @13
    @7
    c.ex
    co
    #
    @13
    cG
    cfv
    #
    c.xp
    co
    #
    c.0
    @13
    cvv
    wcel
    #
    @15
    @30
    wceq
    @27
    vk
    vex
    @31
    @15
    vi
    @13
    @8
    csb
    #
    vi
    @13
    @9
    csb
    #
    c.xp
    co
    @30
    vi
    @13
    @8
    @9
    c.xp
    cvv
    csbov12g
    @31
    @32
    @28
    @33
    @29
    c.xp
    vi
    @13
    @8
    @28
    cvv
    @31
    vi
    @28
    nfcvd
    @6
    @13
    @7
    c.ex
    oveq1
    csbiegf
    @33
    @29
    wceq
    @31
    vi
    @13
    cG
    csbfv
    a1i
    oveq12d
    eqtrd
    mp1i
    @27
    @0
    @4
    @13
    @1
    c2
    caddc
    co
    #
    cuz
    cfv
    wcel
    #
    @30
    c.0
    wceq
    @0
    @4
    @25
    @14
    simplll
    @0
    @4
    @25
    @14
    simpllr
    @27
    @34
    cz
    wcel
    @13
    cz
    wcel
    #
    @34
    @13
    cle
    wbr
    #
    @35
    @27
    @1
    c2
    @26
    @1
    cz
    wcel
    @14
    @26
    @1
    @4
    @23
    @0
    @25
    @2
    @23
    @3
    @24
    adantr
    ad2antlr
    nn0zd
    adantr
    c2
    cz
    wcel
    @27
    2z
    a1i
    zaddcld
    @27
    @13
    @5
    @25
    @14
    simplr
    nn0zd
    @27
    @37
    @11
    c1
    caddc
    co
    #
    @13
    cle
    wbr
    #
    @26
    @14
    @39
    @5
    @11
    cz
    wcel
    @36
    @14
    @39
    wb
    @25
    @5
    @11
    @2
    @12
    @0
    @3
    @2
    @23
    @12
    @24
    @1
    peano2nn0
    syl
    ad2antrl
    nn0zd
    @13
    nn0z
    @11
    @13
    zltp1le
    syl2an
    biimpa
    @26
    @37
    @39
    wb
    #
    @14
    @4
    @40
    @0
    @25
    @2
    @40
    @3
    @2
    @39
    @37
    @2
    @38
    @34
    @13
    cle
    @2
    @1
    cc
    wcel
    @38
    @34
    wceq
    @1
    nncn
    @1
    add1p1
    syl
    breq1d
    bicomd
    adantr
    ad2antlr
    adantr
    mpbird
    @34
    @13
    eluz2
    syl3anbrc
    cA
    cB
    cP
    cR
    cT
    c.xp
    vn
    c.ex
    cG
    @13
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
    chfacfpmmul0
    syl3anc
    eqtrd
    ex
    ralrimiva
    @22
    @18
    vx
    @11
    cn0
    @19
    @11
    wceq
    #
    @21
    @17
    vk
    cn0
    @41
    @20
    @14
    @16
    @19
    @11
    @13
    clt
    breq1
    imbi1d
    ralbidv
    rspcev
    syl2anc
    mptnn0fsupp
end
