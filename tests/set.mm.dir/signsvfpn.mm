include "cc0.mm"
include "cmul.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cmin.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "csgn.mm"
include "recnd.mm"
include "cc.mm"
include "chash.mm"
include "cfzo.mm"
include "cr.mm"
include "cword.mm"
include "wcel.mm"
include "wf.mm"
include "c0.mm"
include "csn.mm"
include "eldifad.mm"
include "wrdf.mm"
include "syl.mm"
include "oveq1i.mm"
include "wne.mm"
include "cn.mm"
include "cdif.mm"
include "eldifsn.mm"
include "sylib.mm"
include "lennncl.mm"
include "fzo0end.mm"
include "3syl.mm"
include "syl5eqel.mm"
include "ffvelrnd.mm"
include "mulcomd.mm"
include "breq2d.mm"
include "wb.mm"
include "sgnmulsgp.mm"
include "syl2anc.mm"
include "bitr3d.mm"
include "biimpa.mm"
include "adantr.mm"
include "simpr.mm"
include "gt0ne0d.mm"
include "mulne0bad.mm"
include "syl5eqner.mm"
include "signsvtn0.mm"
include "fveq2i.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "cxr.mm"
include "rexrd.mm"
include "sgnsgn.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "breqtrrd.mm"
include "sgnclre.mm"
include "eqeltrd.mm"
include "mpbird.mm"
include "eqid.mm"
include "signsvtp.mm"
include "syldan.mm"

theorem signsvfpn
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
  assert |- ( ( ph /\ 0 < ( B x. A ) ) -> ( V ` F ) = ( V ` E ) )

  proof
    wph
    cc0
    cB
    cA
    cmul
    co
    #
    clt
    wbr
    #
    cc0
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
    clt
    wbr
    #
    cF
    cV
    cfv
    cE
    cV
    cfv
    wceq
    wph
    @1
    wa
    #
    @4
    cc0
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
    clt
    wbr
    #
    @5
    cc0
    @6
    cB
    csgn
    cfv
    #
    cmul
    co
    #
    @8
    clt
    wph
    @1
    cc0
    @11
    clt
    wbr
    #
    wph
    cc0
    cA
    cB
    cmul
    co
    #
    clt
    wbr
    #
    @1
    @12
    wph
    @13
    @0
    cc0
    clt
    wph
    cA
    cB
    wph
    cA
    signsvf.a
    recnd
    #
    wph
    cB
    @2
    cE
    cfv
    #
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
    cr
    cword
    #
    wcel
    #
    @18
    cr
    cE
    wf
    wph
    cE
    @19
    c0
    csn
    #
    signsvf.e
    eldifad
    cr
    cE
    wrdf
    syl
    wph
    @2
    @17
    c1
    cmin
    co
    #
    @18
    cN
    @17
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
    @17
    cn
    wcel
    @22
    @18
    wcel
    wph
    cE
    @19
    @21
    cdif
    wcel
    #
    @23
    signsvf.e
    cE
    @19
    c0
    eldifsn
    sylib
    cr
    cE
    lennncl
    @17
    fzo0end
    3syl
    syl5eqel
    ffvelrnd
    #
    recnd
    syl5eqel
    #
    mulcomd
    breq2d
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @14
    @12
    wb
    signsvf.a
    wph
    cB
    @16
    cr
    signsvf.b
    @25
    syl5eqel
    #
    cA
    cB
    sgnmulsgp
    syl2anc
    bitr3d
    biimpa
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
    @24
    @16
    cc0
    wne
    #
    @3
    @10
    wceq
    wph
    @24
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
    @26
    adantr
    wph
    cA
    cc
    wcel
    @1
    @15
    adantr
    @5
    @0
    wph
    @1
    simpr
    gt0ne0d
    mulne0bad
    syl5eqner
    @24
    @31
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
    @30
    @10
    wceq
    @5
    cB
    wph
    @28
    @1
    @29
    adantr
    #
    rexrd
    cB
    sgnsgn
    syl
    eqtrd
    oveq2d
    breqtrrd
    @5
    @27
    @3
    cr
    wcel
    @4
    @9
    wb
    wph
    @27
    @1
    signsvf.a
    adantr
    @5
    @3
    @10
    cr
    @32
    @5
    @28
    @10
    cr
    wcel
    @33
    cB
    sgnclre
    syl
    eqeltrd
    cA
    @3
    sgnmulsgp
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
    signsvtp
    syldan
end
