include "cr.mm"
include "cword.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfzo.mm"
include "wf.mm"
include "wfn.mm"
include "wceq.mm"
include "signshf.mm"
include "ffn.mm"
include "hashfn.mm"
include "3syl.mm"
include "cn0.mm"
include "lencl.mm"
include "adantr.mm"
include "1nn0.mm"
include "a1i.mm"
include "nn0addcld.mm"
include "hashfzo0.mm"
include "syl.mm"
include "eqtrd.mm"

theorem signshlen
  let cC: class C
  let c.pd: class .+^
  let cT: class T
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let cF: class F
  let cH: class H
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let cK: class K
  assume signsv.p: |- .+^ = ( a e. { -u 1 , 0 , 1 } , b e. { -u 1 , 0 , 1 } |-> if ( b = 0 , a , b ) )
  assume signsv.w: |- W = { <. ( Base ` ndx ) , { -u 1 , 0 , 1 } >. , <. ( +g ` ndx ) , .+^ >. }
  assume signsv.t: |- T = ( f e. Word RR |-> ( n e. ( 0 ..^ ( # ` f ) ) |-> ( W gsum ( i e. ( 0 ... n ) |-> ( sgn ` ( f ` i ) ) ) ) ) )
  assume signsv.v: |- V = ( f e. Word RR |-> sum_ j e. ( 1 ..^ ( # ` f ) ) if ( ( ( T ` f ) ` j ) =/= ( ( T ` f ) ` ( j - 1 ) ) , 1 , 0 ) )
  assume signs.h: |- H = ( ( <" 0 "> ++ F ) oF - ( ( F ++ <" 0 "> ) oFC x. C ) )

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
  assert |- ( ( F e. Word RR /\ C e. RR+ ) -> ( # ` H ) = ( ( # ` F ) + 1 ) )

  proof
    cF
    cr
    cword
    wcel
    #
    cC
    crp
    wcel
    #
    wa
    #
    cH
    chash
    cfv
    #
    cc0
    cF
    chash
    cfv
    #
    c1
    caddc
    co
    #
    cfzo
    co
    #
    chash
    cfv
    #
    @5
    @2
    @6
    cr
    cH
    wf
    cH
    @6
    wfn
    @3
    @7
    wceq
    cC
    c.pd
    cT
    vf
    vi
    vj
    vn
    cF
    cH
    cV
    cW
    va
    vb
    signsv.p
    signsv.w
    signsv.t
    signsv.v
    signs.h
    signshf
    @6
    cr
    cH
    ffn
    @6
    cH
    hashfn
    3syl
    @2
    @5
    cn0
    wcel
    @7
    @5
    wceq
    @2
    @4
    c1
    @0
    @4
    cn0
    wcel
    @1
    cr
    cF
    lencl
    adantr
    c1
    cn0
    wcel
    @2
    1nn0
    a1i
    nn0addcld
    @5
    hashfzo0
    syl
    eqtrd
end
