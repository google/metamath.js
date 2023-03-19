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
include "wceq.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "cif.mm"
include "cmpt.mm"
include "c0g.mm"
include "cfsupp.mm"
include "cvv.mm"
include "fvexd.mm"
include "ovex.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ifex.mm"
include "a1i.mm"
include "csb.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "nnnn0.mm"
include "peano2nn0.mm"
include "syl.mm"
include "ad2antrl.mm"
include "simplr.mm"
include "wn.mm"
include "0red.mm"
include "cr.mm"
include "nnre.mm"
include "peano2re.mm"
include "adantr.mm"
include "ad3antlr.mm"
include "nn0re.mm"
include "ad2antlr.mm"
include "nn0p1gt0.mm"
include "simpr.mm"
include "lttrd.mm"
include "gt0ne0d.mm"
include "neneqd.mm"
include "wb.mm"
include "eqeq1.mm"
include "notbid.mm"
include "adantl.mm"
include "mpbird.mm"
include "iffalsed.mm"
include "wne.mm"
include "ltne.mm"
include "sylan.mm"
include "breq2.mm"
include "iftrued.mm"
include "syl6eq.mm"
include "3eqtrd.mm"
include "csbied.mm"
include "ex.mm"
include "ralrimiva.mm"
include "breq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "mptnn0fsupp.mm"
include "syl5eqbr.mm"

theorem chfacffsupp
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let c.xp: class .X.
  let vn: setvar n
  let cG: class G
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cY: class Y
  let c.0: class .0.
  let vs: setvar s
  let vb: setvar b
  let vk: setvar k
  let vl: setvar l
  assume chfacfisf.a: |- A = ( N Mat R )
  assume chfacfisf.b: |- B = ( Base ` A )
  assume chfacfisf.p: |- P = ( Poly1 ` R )
  assume chfacfisf.y: |- Y = ( N Mat P )
  assume chfacfisf.r: |- .X. = ( .r ` Y )
  assume chfacfisf.s: |- .- = ( -g ` Y )
  assume chfacfisf.0: |- .0. = ( 0g ` Y )
  assume chfacfisf.t: |- T = ( N matToPolyMat R )
  assume chfacfisf.g: |- G = ( n e. NN0 |-> if ( n = 0 , ( .0. .- ( ( T ` M ) .X. ( T ` ( b ` 0 ) ) ) ) , if ( n = ( s + 1 ) , ( T ` ( b ` s ) ) , if ( ( s + 1 ) < n , .0. , ( ( T ` ( b ` ( n - 1 ) ) ) .- ( ( T ` M ) .X. ( T ` ( b ` n ) ) ) ) ) ) ) )

  disjoint B n
  disjoint M n
  disjoint N n
  disjoint R n
  disjoint Y n
  disjoint b n
  disjoint n s
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
  assert |- ( ( ( N e. Fin /\ R e. CRing /\ M e. B ) /\ ( s e. NN /\ b e. ( B ^m ( 0 ... s ) ) ) ) -> G finSupp ( 0g ` Y ) )

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
    #
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
    cG
    vn
    cn0
    vn
    cv
    #
    cc0
    wceq
    #
    c.0
    cM
    cT
    cfv
    #
    cc0
    @3
    cfv
    cT
    cfv
    c.xp
    co
    #
    c.mi
    co
    #
    @7
    @1
    c1
    caddc
    co
    #
    wceq
    #
    @1
    @3
    cfv
    #
    cT
    cfv
    #
    @12
    @7
    clt
    wbr
    #
    c.0
    @7
    c1
    cmin
    co
    @3
    cfv
    cT
    cfv
    #
    @9
    @7
    @3
    cfv
    cT
    cfv
    c.xp
    co
    #
    c.mi
    co
    #
    cif
    #
    cif
    #
    cif
    #
    cmpt
    cY
    c0g
    cfv
    #
    cfsupp
    chfacfisf.g
    @6
    vk
    cvv
    @22
    vn
    cvv
    @23
    vl
    @6
    cY
    c0g
    fvexd
    @22
    cvv
    wcel
    @6
    @7
    cn0
    wcel
    wa
    @8
    @11
    @21
    c.0
    @10
    c.mi
    ovex
    @13
    @15
    @20
    @14
    cT
    fvex
    @16
    c.0
    @19
    c.0
    @23
    cvv
    chfacfisf.0
    cY
    c0g
    fvex
    eqeltri
    @17
    @18
    c.mi
    ovex
    ifex
    ifex
    ifex
    a1i
    @6
    @12
    cn0
    wcel
    #
    @12
    vk
    cv
    #
    clt
    wbr
    #
    vn
    @25
    @22
    csb
    @23
    wceq
    #
    wi
    #
    vk
    cn0
    wral
    #
    vl
    cv
    #
    @25
    clt
    wbr
    #
    @27
    wi
    #
    vk
    cn0
    wral
    #
    vl
    cn0
    wrex
    @2
    @24
    @0
    @4
    @2
    @1
    cn0
    wcel
    #
    @24
    @1
    nnnn0
    #
    @1
    peano2nn0
    syl
    ad2antrl
    @6
    @28
    vk
    cn0
    @6
    @25
    cn0
    wcel
    #
    wa
    #
    @26
    @27
    @37
    @26
    wa
    #
    vn
    @25
    @22
    @23
    cn0
    @6
    @36
    @26
    simplr
    @38
    @7
    @25
    wceq
    #
    wa
    #
    @22
    @21
    @20
    @23
    @40
    @8
    @11
    @21
    @40
    @8
    wn
    #
    @25
    cc0
    wceq
    #
    wn
    #
    @38
    @43
    @39
    @38
    @25
    cc0
    @38
    @25
    @38
    cc0
    @12
    @25
    @38
    0red
    @5
    @12
    cr
    wcel
    #
    @0
    @36
    @26
    @2
    @44
    @4
    @2
    @1
    cr
    wcel
    @44
    @1
    nnre
    @1
    peano2re
    syl
    adantr
    #
    ad3antlr
    @36
    @25
    cr
    wcel
    @6
    @26
    @25
    nn0re
    ad2antlr
    @37
    cc0
    @12
    clt
    wbr
    #
    @26
    @37
    @34
    @46
    @5
    @34
    @0
    @36
    @2
    @34
    @4
    @35
    adantr
    ad2antlr
    @1
    nn0p1gt0
    syl
    adantr
    @37
    @26
    simpr
    lttrd
    gt0ne0d
    neneqd
    adantr
    @39
    @41
    @43
    wb
    @38
    @39
    @8
    @42
    @7
    @25
    cc0
    eqeq1
    notbid
    adantl
    mpbird
    iffalsed
    @40
    @13
    @15
    @20
    @40
    @13
    wn
    #
    @25
    @12
    wceq
    #
    wn
    #
    @38
    @49
    @39
    @38
    @25
    @12
    @37
    @44
    @26
    @25
    @12
    wne
    @5
    @44
    @0
    @36
    @45
    ad2antlr
    @12
    @25
    ltne
    sylan
    neneqd
    adantr
    @39
    @47
    @49
    wb
    @38
    @39
    @13
    @48
    @7
    @25
    @12
    eqeq1
    notbid
    adantl
    mpbird
    iffalsed
    @40
    @20
    c.0
    @23
    @40
    @16
    c.0
    @19
    @40
    @16
    @26
    @37
    @26
    @39
    simplr
    @39
    @16
    @26
    wb
    @38
    @7
    @25
    @12
    clt
    breq2
    adantl
    mpbird
    iftrued
    chfacfisf.0
    syl6eq
    3eqtrd
    csbied
    ex
    ralrimiva
    @33
    @29
    vl
    @12
    cn0
    @30
    @12
    wceq
    #
    @32
    @28
    vk
    cn0
    @50
    @31
    @26
    @27
    @30
    @12
    @25
    clt
    breq1
    imbi1d
    ralbidv
    rspcev
    syl2anc
    mptnn0fsupp
    syl5eqbr
end
