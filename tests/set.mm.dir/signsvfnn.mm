include "cmul.mm"
include "co.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cmin.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "csgn.mm"
include "cr.mm"
include "cword.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "wne.mm"
include "adantr.mm"
include "cc.mm"
include "chash.mm"
include "cfzo.mm"
include "wf.mm"
include "eldifad.mm"
include "wrdf.mm"
include "syl.mm"
include "oveq1i.mm"
include "cn.mm"
include "eldifsn.mm"
include "sylib.mm"
include "lennncl.mm"
include "fzo0end.mm"
include "3syl.mm"
include "syl5eqel.mm"
include "ffvelrnd.mm"
include "recnd.mm"
include "simpr.mm"
include "lt0ne0d.mm"
include "mulne0bad.mm"
include "syl5eqner.mm"
include "signsvtn0.mm"
include "fveq2i.mm"
include "syl6eqr.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "cxr.mm"
include "rexrd.mm"
include "sgnsgn.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "mulcomd.mm"
include "breq1d.mm"
include "wb.mm"
include "sgnmulsgn.mm"
include "bitr3d.mm"
include "biimpa.mm"
include "eqbrtrd.mm"
include "sgnclre.mm"
include "eqeltrd.mm"
include "mpbird.mm"
include "eqid.mm"
include "signsvtn.mm"
include "syldan.mm"

theorem signsvfnn
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.pd: class .+^
  let cT: class T
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cN: class N
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let cK: class K
  assume signsv.p: |- .+^ = ( a e. { -u 1 , 0 , 1 } , b e. { -u 1 , 0 , 1 } |-> if ( b = 0 , a , b ) )
  assume signsv.w: |- W = { <. ( Base ` ndx ) , { -u 1 , 0 , 1 } >. , <. ( +g ` ndx ) , .+^ >. }
  assume signsv.t: |- T = ( f e. Word RR |-> ( n e. ( 0 ..^ ( # ` f ) ) |-> ( W gsum ( i e. ( 0 ... n ) |-> ( sgn ` ( f ` i ) ) ) ) ) )
  assume signsv.v: |- V = ( f e. Word RR |-> sum_ j e. ( 1 ..^ ( # ` f ) ) if ( ( ( T ` f ) ` j ) =/= ( ( T ` f ) ` ( j - 1 ) ) , 1 , 0 ) )
  assume signsvf.e: |- ( ph -> E e. ( Word RR \ { (/) } ) )
  assume signsvf.0: |- ( ph -> ( E ` 0 ) =/= 0 )
  assume signsvf.f: |- ( ph -> F = ( E ++ <" A "> ) )
  assume signsvf.a: |- ( ph -> A e. RR )
  assume signsvf.n: |- N = ( # ` E )
  assume signsvf.b: |- B = ( E ` ( N - 1 ) )

  disjoint a b
  disjoint a f
  disjoint a i
  disjoint a j
  disjoint a n
  disjoint A a
  disjoint b f
  disjoint b i
  disjoint b j
  disjoint b n
  disjoint A b
  disjoint f i
  disjoint f j
  disjoint f n
  disjoint A f
  disjoint i j
  disjoint i n
  disjoint A i
  disjoint j n
  disjoint A j
  disjoint A n
  disjoint E a
  disjoint E b
  disjoint E f
  disjoint E i
  disjoint E j
  disjoint E n
  disjoint N a
  disjoint N b
  disjoint N f
  disjoint N i
  disjoint N n
  disjoint T a
  disjoint T b
  disjoint T f
  disjoint T j
  disjoint T n
  disjoint a b
  disjoint .+^ a
  disjoint .+^ b
  disjoint f i
  disjoint f n
  disjoint F f
  disjoint i n
  disjoint F i
  disjoint F n
  disjoint W f
  disjoint W i
  disjoint W n
  disjoint K f
  disjoint K i
  disjoint K n
  assert |- ( ( ph /\ ( B x. A ) < 0 ) -> ( ( V ` F ) - ( V ` E ) ) = 1 )

  proof
    wph
    cB
    cA
    cmul
    co
    #
    cc0
    clt
    wbr
    #
    cA
    cN
    c1
    cmin
    co
    #
    cE
    cT
    cfv
    cfv
    #
    cmul
    co
    cc0
    clt
    wbr
    #
    cF
    cV
    cfv
    cE
    cV
    cfv
    cmin
    co
    c1
    wceq
    wph
    @1
    wa
    #
    @4
    cA
    csgn
    cfv
    #
    @3
    csgn
    cfv
    #
    cmul
    co
    #
    cc0
    clt
    wbr
    #
    @5
    @8
    @6
    cB
    csgn
    cfv
    #
    cmul
    co
    #
    cc0
    clt
    @5
    @7
    @10
    @6
    cmul
    @5
    @7
    @10
    csgn
    cfv
    #
    @10
    @5
    @3
    @10
    csgn
    @5
    cE
    cr
    cword
    #
    c0
    csn
    #
    cdif
    wcel
    #
    @2
    cE
    cfv
    #
    cc0
    wne
    #
    @3
    @10
    wceq
    wph
    @15
    @1
    signsvf.e
    adantr
    @5
    @16
    cB
    cc0
    signsvf.b
    @5
    cB
    cA
    wph
    cB
    cc
    wcel
    @1
    wph
    cB
    @16
    cc
    signsvf.b
    wph
    @16
    wph
    cc0
    cE
    chash
    cfv
    #
    cfzo
    co
    #
    cr
    @2
    cE
    wph
    cE
    @13
    wcel
    #
    @19
    cr
    cE
    wf
    wph
    cE
    @13
    @14
    signsvf.e
    eldifad
    cr
    cE
    wrdf
    syl
    wph
    @2
    @18
    c1
    cmin
    co
    #
    @19
    cN
    @18
    c1
    cmin
    signsvf.n
    oveq1i
    wph
    @20
    cE
    c0
    wne
    wa
    #
    @18
    cn
    wcel
    @21
    @19
    wcel
    wph
    @15
    @22
    signsvf.e
    cE
    @13
    c0
    eldifsn
    sylib
    cr
    cE
    lennncl
    @18
    fzo0end
    3syl
    syl5eqel
    ffvelrnd
    #
    recnd
    syl5eqel
    #
    adantr
    wph
    cA
    cc
    wcel
    @1
    wph
    cA
    signsvf.a
    recnd
    #
    adantr
    @5
    @0
    wph
    @1
    simpr
    lt0ne0d
    mulne0bad
    syl5eqner
    @15
    @17
    wa
    @3
    @16
    csgn
    cfv
    @10
    c.pd
    cT
    vf
    vi
    vj
    vn
    cE
    cN
    cV
    cW
    va
    vb
    signsv.p
    signsv.w
    signsv.t
    signsv.v
    signsvf.n
    signsvtn0
    cB
    @16
    csgn
    signsvf.b
    fveq2i
    syl6eqr
    syl2anc
    #
    fveq2d
    @5
    cB
    cxr
    wcel
    @12
    @10
    wceq
    @5
    cB
    wph
    cB
    cr
    wcel
    #
    @1
    wph
    cB
    @16
    cr
    signsvf.b
    @23
    syl5eqel
    #
    adantr
    #
    rexrd
    cB
    sgnsgn
    syl
    eqtrd
    oveq2d
    wph
    @1
    @11
    cc0
    clt
    wbr
    #
    wph
    cA
    cB
    cmul
    co
    #
    cc0
    clt
    wbr
    #
    @1
    @30
    wph
    @31
    @0
    cc0
    clt
    wph
    cA
    cB
    @25
    @24
    mulcomd
    breq1d
    wph
    cA
    cr
    wcel
    #
    @27
    @32
    @30
    wb
    signsvf.a
    @28
    cA
    cB
    sgnmulsgn
    syl2anc
    bitr3d
    biimpa
    eqbrtrd
    @5
    @33
    @3
    cr
    wcel
    @4
    @9
    wb
    wph
    @33
    @1
    signsvf.a
    adantr
    @5
    @3
    @10
    cr
    @26
    @5
    @27
    @10
    cr
    wcel
    @29
    cB
    sgnclre
    syl
    eqeltrd
    cA
    @3
    sgnmulsgn
    syl2anc
    mpbird
    wph
    cA
    @3
    c.pd
    cT
    vf
    vi
    vj
    vn
    cE
    cF
    cN
    cV
    cW
    va
    vb
    signsv.p
    signsv.w
    signsv.t
    signsv.v
    signsvf.e
    signsvf.0
    signsvf.f
    signsvf.a
    signsvf.n
    @3
    eqid
    signsvtn
    syldan
end
