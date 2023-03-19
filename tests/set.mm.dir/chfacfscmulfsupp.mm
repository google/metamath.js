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
include "peano2nn0.mm"
include "syl.mm"
include "ad2antrl.mm"
include "vex.mm"
include "csbov12g.mm"
include "csbov1g.mm"
include "csbvarg.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "csbfv.mm"
include "oveq12d.mm"
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
include "chfacfscmul0.mm"
include "syl3anc.mm"
include "ex.mm"
include "ralrimiva.mm"
include "breq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "mptnn0fsupp.mm"

theorem chfacfscmulfsupp
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let c.x: class .x.
  let c.xp: class .X.
  let vi: setvar i
  let vn: setvar n
  let c.ex: class .^
  let cG: class G
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vs: setvar s
  let vb: setvar b
  let vk: setvar k
  let vl: setvar l
  let cK: class K
  let vz: setvar z
  assume chfacfisf.a: |- A = ( N Mat R )
  assume chfacfisf.b: |- B = ( Base ` A )
  assume chfacfisf.p: |- P = ( Poly1 ` R )
  assume chfacfisf.y: |- Y = ( N Mat P )
  assume chfacfisf.r: |- .X. = ( .r ` Y )
  assume chfacfisf.s: |- .- = ( -g ` Y )
  assume chfacfisf.0: |- .0. = ( 0g ` Y )
  assume chfacfisf.t: |- T = ( N matToPolyMat R )
  assume chfacfisf.g: |- G = ( n e. NN0 |-> if ( n = 0 , ( .0. .- ( ( T ` M ) .X. ( T ` ( b ` 0 ) ) ) ) , if ( n = ( s + 1 ) , ( T ` ( b ` s ) ) , if ( ( s + 1 ) < n , .0. , ( ( T ` ( b ` ( n - 1 ) ) ) .- ( ( T ` M ) .X. ( T ` ( b ` n ) ) ) ) ) ) ) )
  assume chfacfscmulcl.x: |- X = ( var1 ` R )
  assume chfacfscmulcl.m: |- .x. = ( .s ` Y )
  assume chfacfscmulcl.e: |- .^ = ( .g ` ( mulGrp ` P ) )

  disjoint B n
  disjoint M n
  disjoint N n
  disjoint R n
  disjoint Y n
  disjoint b n
  disjoint n s
  disjoint B s
  disjoint .0. n
  disjoint B i
  disjoint i s
  disjoint G i
  disjoint M i
  disjoint N i
  disjoint R i
  disjoint X i
  disjoint Y i
  disjoint .^ i
  disjoint .x. b
  disjoint .x. i
  disjoint b i
  disjoint B k
  disjoint B l
  disjoint k l
  disjoint M k
  disjoint M l
  disjoint N k
  disjoint N l
  disjoint R k
  disjoint R l
  disjoint T k
  disjoint T l
  disjoint Y k
  disjoint Y l
  disjoint b k
  disjoint b l
  disjoint k n
  disjoint k s
  disjoint l n
  disjoint l s
  disjoint .X. k
  disjoint .X. l
  disjoint .0. k
  disjoint .0. l
  disjoint .- k
  disjoint .- l
  disjoint K n
  disjoint B z
  disjoint k z
  disjoint s z
  disjoint G k
  disjoint G z
  disjoint i k
  disjoint i z
  disjoint M z
  disjoint N z
  disjoint R z
  disjoint X k
  disjoint X z
  disjoint .0. z
  disjoint .^ k
  disjoint .^ z
  disjoint .x. k
  disjoint .x. z
  disjoint b z
  assert |- ( ( ( N e. Fin /\ R e. CRing /\ M e. B ) /\ ( s e. NN /\ b e. ( B ^m ( 0 ... s ) ) ) ) -> ( i e. NN0 |-> ( ( i .^ X ) .x. ( G ` i ) ) ) finSupp .0. )

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
    cX
    c.ex
    co
    #
    @6
    cG
    cfv
    #
    c.x
    co
    #
    vi
    cvv
    c.0
    vz
    c.0
    cvv
    wcel
    @5
    c.0
    cY
    c0g
    cfv
    cvv
    chfacfisf.0
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
    @7
    @8
    c.x
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
    @10
    vk
    cv
    #
    clt
    wbr
    #
    vi
    @12
    @9
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
    vz
    cv
    #
    @12
    clt
    wbr
    #
    @15
    wi
    #
    vk
    cn0
    wral
    #
    vz
    cn0
    wrex
    @2
    @11
    @0
    @3
    @2
    @1
    cn0
    wcel
    #
    @11
    @1
    nnnn0
    #
    @1
    peano2nn0
    syl
    ad2antrl
    #
    @5
    @16
    vk
    cn0
    @5
    @12
    cn0
    wcel
    #
    wa
    #
    @13
    @15
    @26
    @13
    wa
    #
    @14
    @12
    cX
    c.ex
    co
    #
    @12
    cG
    cfv
    #
    c.x
    co
    #
    c.0
    @12
    cvv
    wcel
    #
    @14
    @30
    wceq
    @27
    vk
    vex
    @31
    @14
    vi
    @12
    @7
    csb
    #
    vi
    @12
    @8
    csb
    #
    c.x
    co
    @30
    vi
    @12
    @7
    @8
    c.x
    cvv
    csbov12g
    @31
    @32
    @28
    @33
    @29
    c.x
    @31
    @32
    vi
    @12
    @6
    csb
    #
    cX
    c.ex
    co
    @28
    vi
    @12
    @6
    cX
    c.ex
    cvv
    csbov1g
    @31
    @34
    @12
    cX
    c.ex
    vi
    @12
    cvv
    csbvarg
    oveq1d
    eqtrd
    @33
    @29
    wceq
    @31
    vi
    @12
    cG
    csbfv
    a1i
    oveq12d
    eqtrd
    mp1i
    @27
    @0
    @4
    @12
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
    @13
    simplll
    @0
    @4
    @25
    @13
    simpllr
    @27
    @35
    cz
    wcel
    @12
    cz
    wcel
    #
    @35
    @12
    cle
    wbr
    #
    @36
    @27
    @1
    c2
    @26
    @1
    cz
    wcel
    @13
    @26
    @1
    @4
    @22
    @0
    @25
    @2
    @22
    @3
    @23
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
    @12
    @5
    @25
    @13
    simplr
    nn0zd
    @27
    @38
    @10
    c1
    caddc
    co
    #
    @12
    cle
    wbr
    #
    @26
    @13
    @40
    @5
    @10
    cz
    wcel
    @37
    @13
    @40
    wb
    @25
    @5
    @10
    @24
    nn0zd
    @12
    nn0z
    @10
    @12
    zltp1le
    syl2an
    biimpa
    @26
    @38
    @40
    wb
    #
    @13
    @4
    @41
    @0
    @25
    @2
    @41
    @3
    @2
    @40
    @38
    @2
    @39
    @35
    @12
    cle
    @2
    @1
    cc
    wcel
    @39
    @35
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
    @35
    @12
    eluz2
    syl3anbrc
    cA
    cB
    cP
    cR
    cT
    c.x
    c.xp
    vn
    c.ex
    cG
    @12
    cM
    c.mi
    cN
    cX
    cY
    c.0
    vs
    vb
    chfacfisf.a
    chfacfisf.b
    chfacfisf.p
    chfacfisf.y
    chfacfisf.r
    chfacfisf.s
    chfacfisf.0
    chfacfisf.t
    chfacfisf.g
    chfacfscmulcl.x
    chfacfscmulcl.m
    chfacfscmulcl.e
    chfacfscmul0
    syl3anc
    eqtrd
    ex
    ralrimiva
    @21
    @17
    vz
    @10
    cn0
    @18
    @10
    wceq
    #
    @20
    @16
    vk
    cn0
    @42
    @19
    @13
    @15
    @18
    @10
    @12
    clt
    breq1
    imbi1d
    ralbidv
    rspcev
    syl2anc
    mptnn0fsupp
end
