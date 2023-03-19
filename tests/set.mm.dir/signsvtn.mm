include "cmul.mm"
include "co.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cfv.mm"
include "cmin.mm"
include "c1.mm"
include "wceq.mm"
include "caddc.mm"
include "chash.mm"
include "cif.mm"
include "cs1.mm"
include "cconcat.mm"
include "fveq2d.mm"
include "cr.mm"
include "cword.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "wne.mm"
include "signsvfn.mm"
include "syl21anc.mm"
include "eqtrd.mm"
include "adantr.mm"
include "oveq1i.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "cfzo.mm"
include "wf.mm"
include "eldifad.mm"
include "signstf.mm"
include "wrdf.mm"
include "3syl.mm"
include "cn.mm"
include "eldifsn.mm"
include "sylib.mm"
include "lennncl.mm"
include "fzo0end.mm"
include "signstlen.mm"
include "syl.mm"
include "oveq2d.mm"
include "eleqtrrd.mm"
include "ffvelrnd.mm"
include "syl5eqel.mm"
include "recnd.mm"
include "mulcomd.mm"
include "simpr.mm"
include "eqbrtrd.mm"
include "syl5eqbrr.mm"
include "iftrued.mm"
include "eqtr2d.mm"
include "cn0.mm"
include "signsvvf.mm"
include "a1i.mm"
include "s1cld.mm"
include "ccatcl.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "nn0cnd.mm"
include "1cnd.mm"
include "subaddd.mm"
include "mpbird.mm"

theorem signsvtn
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
  assume signsvt.b: |- B = ( ( T ` E ) ` ( N - 1 ) )

  disjoint a b
  disjoint a f
  disjoint a i
  disjoint a j
  disjoint b f
  disjoint b i
  disjoint b j
  disjoint f i
  disjoint f j
  disjoint i j
  disjoint a n
  disjoint A a
  disjoint b n
  disjoint A b
  disjoint f n
  disjoint A f
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
  assert |- ( ( ph /\ ( A x. B ) < 0 ) -> ( ( V ` F ) - ( V ` E ) ) = 1 )

  proof
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
    wa
    #
    cF
    cV
    cfv
    #
    cE
    cV
    cfv
    #
    cmin
    co
    c1
    wceq
    @4
    c1
    caddc
    co
    #
    @3
    wceq
    @2
    @3
    @4
    cE
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cE
    cT
    cfv
    #
    cfv
    #
    cA
    cmul
    co
    #
    cc0
    clt
    wbr
    #
    c1
    cc0
    cif
    #
    caddc
    co
    #
    @5
    wph
    @3
    @13
    wceq
    @1
    wph
    @3
    cE
    cA
    cs1
    #
    cconcat
    co
    #
    cV
    cfv
    #
    @13
    wph
    cF
    @15
    cV
    signsvf.f
    fveq2d
    wph
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
    cc0
    cE
    cfv
    cc0
    wne
    cA
    cr
    wcel
    #
    @16
    @13
    wceq
    signsvf.e
    signsvf.0
    signsvf.a
    c.pd
    cT
    vf
    vi
    vj
    vn
    cE
    cA
    cV
    cW
    va
    vb
    signsv.p
    signsv.w
    signsv.t
    signsv.v
    signsvfn
    syl21anc
    eqtrd
    adantr
    @2
    @12
    c1
    @4
    caddc
    @2
    @11
    c1
    cc0
    @2
    @10
    cB
    cA
    cmul
    co
    #
    cc0
    clt
    cB
    @9
    cA
    cmul
    cB
    cN
    c1
    cmin
    co
    #
    @8
    cfv
    @9
    signsvt.b
    @22
    @7
    @8
    cN
    @6
    c1
    cmin
    signsvf.n
    oveq1i
    fveq2i
    eqtri
    #
    oveq1i
    @2
    @21
    @0
    cc0
    clt
    @2
    cB
    cA
    @2
    cB
    @2
    cB
    @9
    cr
    @23
    @2
    cc0
    @8
    chash
    cfv
    #
    cfzo
    co
    #
    cr
    @7
    @8
    @2
    cE
    @17
    wcel
    #
    @8
    @17
    wcel
    @25
    cr
    @8
    wf
    @2
    cE
    @17
    @18
    wph
    @19
    @1
    signsvf.e
    adantr
    eldifad
    #
    c.pd
    cT
    vf
    vi
    vj
    vn
    cE
    cV
    cW
    va
    vb
    signsv.p
    signsv.w
    signsv.t
    signsv.v
    signstf
    cr
    @8
    wrdf
    3syl
    @2
    @7
    cc0
    @6
    cfzo
    co
    #
    @25
    @2
    @26
    cE
    c0
    wne
    wa
    #
    @6
    cn
    wcel
    @7
    @28
    wcel
    wph
    @29
    @1
    wph
    @19
    @29
    signsvf.e
    cE
    @17
    c0
    eldifsn
    sylib
    adantr
    cr
    cE
    lennncl
    @6
    fzo0end
    3syl
    @2
    @24
    @6
    cc0
    cfzo
    @2
    @26
    @24
    @6
    wceq
    @27
    c.pd
    cT
    vf
    vi
    vj
    vn
    cE
    cV
    cW
    va
    vb
    signsv.p
    signsv.w
    signsv.t
    signsv.v
    signstlen
    syl
    oveq2d
    eleqtrrd
    ffvelrnd
    syl5eqel
    recnd
    @2
    cA
    wph
    @20
    @1
    signsvf.a
    adantr
    #
    recnd
    mulcomd
    wph
    @1
    simpr
    eqbrtrd
    syl5eqbrr
    iftrued
    oveq2d
    eqtr2d
    @2
    @3
    @4
    c1
    @2
    @3
    @2
    @17
    cn0
    cF
    cV
    @17
    cn0
    cV
    wf
    @2
    c.pd
    cT
    vf
    vi
    vj
    vn
    cV
    cW
    va
    vb
    signsv.p
    signsv.w
    signsv.t
    signsv.v
    signsvvf
    a1i
    #
    @2
    cF
    @15
    @17
    wph
    cF
    @15
    wceq
    @1
    signsvf.f
    adantr
    @2
    @26
    @14
    @17
    wcel
    @15
    @17
    wcel
    @27
    @2
    cA
    cr
    @30
    s1cld
    cr
    cE
    @14
    ccatcl
    syl2anc
    eqeltrd
    ffvelrnd
    nn0cnd
    @2
    @4
    @2
    @17
    cn0
    cE
    cV
    @31
    @27
    ffvelrnd
    nn0cnd
    @2
    1cnd
    subaddd
    mpbird
end
