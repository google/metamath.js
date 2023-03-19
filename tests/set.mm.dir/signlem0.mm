include "cr.mm"
include "cword.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "cc0.mm"
include "cfv.mm"
include "wne.mm"
include "wa.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "chash.mm"
include "c1.mm"
include "cmin.mm"
include "cmul.mm"
include "clt.mm"
include "wbr.mm"
include "cif.mm"
include "caddc.mm"
include "wceq.mm"
include "0re.mm"
include "signsvfn.mm"
include "mpan2.mm"
include "ltnri.mm"
include "cneg.mm"
include "cpr.mm"
include "cc.mm"
include "wss.mm"
include "neg1cn.mm"
include "ax-1cn.mm"
include "prssi.mm"
include "mp2an.mm"
include "cfzo.mm"
include "cn.mm"
include "simpl.mm"
include "eldifsn.mm"
include "sylib.mm"
include "lennncl.mm"
include "fzo0end.mm"
include "3syl.mm"
include "signstfvcl.mm"
include "mpdan.mm"
include "sseldi.mm"
include "mul01d.mm"
include "breq1d.mm"
include "mtbiri.mm"
include "iffalsed.mm"
include "oveq2d.mm"
include "cn0.mm"
include "wf.mm"
include "signsvvf.mm"
include "a1i.mm"
include "eldifad.mm"
include "ffvelrnd.mm"
include "nn0cnd.mm"
include "addid1d.mm"
include "3eqtrd.mm"

theorem signlem0
  let c.pd: class .+^
  let cT: class T
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let cF: class F
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let cK: class K
  assume signsv.p: |- .+^ = ( a e. { -u 1 , 0 , 1 } , b e. { -u 1 , 0 , 1 } |-> if ( b = 0 , a , b ) )
  assume signsv.w: |- W = { <. ( Base ` ndx ) , { -u 1 , 0 , 1 } >. , <. ( +g ` ndx ) , .+^ >. }
  assume signsv.t: |- T = ( f e. Word RR |-> ( n e. ( 0 ..^ ( # ` f ) ) |-> ( W gsum ( i e. ( 0 ... n ) |-> ( sgn ` ( f ` i ) ) ) ) ) )
  assume signsv.v: |- V = ( f e. Word RR |-> sum_ j e. ( 1 ..^ ( # ` f ) ) if ( ( ( T ` f ) ` j ) =/= ( ( T ` f ) ` ( j - 1 ) ) , 1 , 0 ) )

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
  disjoint F a
  disjoint F b
  disjoint F j
  disjoint a n
  disjoint T a
  disjoint b n
  disjoint T b
  disjoint f n
  disjoint T f
  disjoint j n
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
  assert |- ( ( F e. ( Word RR \ { (/) } ) /\ ( F ` 0 ) =/= 0 ) -> ( V ` ( F ++ <" 0 "> ) ) = ( V ` F ) )

  proof
    cF
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
    cF
    cfv
    cc0
    wne
    #
    wa
    #
    cF
    cc0
    cs1
    cconcat
    co
    cV
    cfv
    #
    cF
    cV
    cfv
    #
    cF
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cF
    cT
    cfv
    cfv
    #
    cc0
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
    @6
    cc0
    caddc
    co
    @6
    @4
    cc0
    cr
    wcel
    @5
    @13
    wceq
    0re
    c.pd
    cT
    vf
    vi
    vj
    vn
    cF
    cc0
    cV
    cW
    va
    vb
    signsv.p
    signsv.w
    signsv.t
    signsv.v
    signsvfn
    mpan2
    @4
    @12
    cc0
    @6
    caddc
    @4
    @11
    c1
    cc0
    @4
    @11
    cc0
    cc0
    clt
    wbr
    cc0
    0re
    ltnri
    @4
    @10
    cc0
    cc0
    clt
    @4
    @9
    @4
    c1
    cneg
    #
    c1
    cpr
    #
    cc
    @9
    @14
    cc
    wcel
    c1
    cc
    wcel
    @15
    cc
    wss
    neg1cn
    ax-1cn
    @14
    c1
    cc
    prssi
    mp2an
    @4
    @8
    cc0
    @7
    cfzo
    co
    wcel
    #
    @9
    @15
    wcel
    @4
    cF
    @0
    wcel
    cF
    c0
    wne
    wa
    #
    @7
    cn
    wcel
    @16
    @4
    @2
    @17
    @2
    @3
    simpl
    #
    cF
    @0
    c0
    eldifsn
    sylib
    cr
    cF
    lennncl
    @7
    fzo0end
    3syl
    c.pd
    cT
    vf
    vi
    vj
    vn
    cF
    @8
    cV
    cW
    va
    vb
    signsv.p
    signsv.w
    signsv.t
    signsv.v
    signstfvcl
    mpdan
    sseldi
    mul01d
    breq1d
    mtbiri
    iffalsed
    oveq2d
    @4
    @6
    @4
    @6
    @4
    @0
    cn0
    cF
    cV
    @0
    cn0
    cV
    wf
    @4
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
    @4
    cF
    @0
    @1
    @18
    eldifad
    ffvelrnd
    nn0cnd
    addid1d
    3eqtrd
end
