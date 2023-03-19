include "cc0.mm"
include "cmul.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cfv.mm"
include "chash.mm"
include "c1.mm"
include "cmin.mm"
include "cif.mm"
include "caddc.mm"
include "wceq.mm"
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
include "0red.mm"
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
include "remulcld.mm"
include "simpr.mm"
include "oveq1i.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "syl5eqel.mm"
include "recnd.mm"
include "mulcomd.mm"
include "breqtrrd.mm"
include "syl6breq.mm"
include "ltnsymd.mm"
include "iffalsed.mm"
include "cn0.mm"
include "signsvvf.mm"
include "a1i.mm"
include "nn0cnd.mm"
include "addid1d.mm"
include "3eqtrd.mm"

theorem signsvtp
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
  assert |- ( ( ph /\ 0 < ( A x. B ) ) -> ( V ` F ) = ( V ` E ) )

  proof
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
    @4
    cc0
    caddc
    co
    @4
    wph
    @3
    @12
    wceq
    @1
    wph
    @3
    cE
    cA
    cs1
    cconcat
    co
    #
    cV
    cfv
    #
    @12
    wph
    cF
    @13
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
    @14
    @12
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
    @11
    cc0
    @4
    caddc
    @2
    @10
    c1
    cc0
    @2
    cc0
    @9
    @2
    0red
    @2
    @8
    cA
    @2
    cc0
    @7
    chash
    cfv
    #
    cfzo
    co
    #
    cr
    @6
    @7
    @2
    cE
    @15
    wcel
    #
    @7
    @15
    wcel
    @20
    cr
    @7
    wf
    @2
    cE
    @15
    @16
    wph
    @17
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
    @7
    wrdf
    3syl
    @2
    @6
    cc0
    @5
    cfzo
    co
    #
    @20
    @2
    @21
    cE
    c0
    wne
    wa
    #
    @5
    cn
    wcel
    @6
    @23
    wcel
    wph
    @24
    @1
    wph
    @17
    @24
    signsvf.e
    cE
    @15
    c0
    eldifsn
    sylib
    adantr
    cr
    cE
    lennncl
    @5
    fzo0end
    3syl
    @2
    @19
    @5
    cc0
    cfzo
    @2
    @21
    @19
    @5
    wceq
    @22
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
    #
    wph
    @18
    @1
    signsvf.a
    adantr
    #
    remulcld
    @2
    cc0
    cB
    cA
    cmul
    co
    #
    @9
    clt
    @2
    cc0
    @0
    @27
    clt
    wph
    @1
    simpr
    @2
    cB
    cA
    @2
    cB
    @2
    cB
    @8
    cr
    cB
    cN
    c1
    cmin
    co
    #
    @7
    cfv
    @8
    signsvt.b
    @28
    @6
    @7
    cN
    @5
    c1
    cmin
    signsvf.n
    oveq1i
    fveq2i
    eqtri
    #
    @25
    syl5eqel
    recnd
    @2
    cA
    @26
    recnd
    mulcomd
    breqtrrd
    cB
    @8
    cA
    cmul
    @29
    oveq1i
    syl6breq
    ltnsymd
    iffalsed
    oveq2d
    @2
    @4
    @2
    @4
    @2
    @15
    cn0
    cE
    cV
    @15
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
    @22
    ffvelrnd
    nn0cnd
    addid1d
    3eqtrd
end
