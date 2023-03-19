include "cr.mm"
include "cword.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfzo.mm"
include "cs1.mm"
include "cconcat.mm"
include "cmul.mm"
include "cofc.mm"
include "cmin.mm"
include "cof.mm"
include "wf.mm"
include "cvv.mm"
include "cv.mm"
include "resubcl.mm"
include "adantl.mm"
include "0red.mm"
include "s1cld.mm"
include "simpl.mm"
include "ccatcl.mm"
include "syl2anc.mm"
include "wrdf.mm"
include "syl.mm"
include "wceq.mm"
include "ccatlen.mm"
include "s1len.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "1cnd.mm"
include "cfn.mm"
include "cn0.mm"
include "wrdfin.mm"
include "hashcl.mm"
include "3syl.mm"
include "nn0cnd.mm"
include "addcomd.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "feq2d.mm"
include "mpbid.mm"
include "remulcl.mm"
include "syldan.mm"
include "oveq2i.mm"
include "ovexd.mm"
include "simpr.mm"
include "rpred.mm"
include "ofcf.mm"
include "inidm.mm"
include "off.mm"
include "feq1i.mm"
include "sylibr.mm"

theorem signshf
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
  let vx: setvar x
  let vy: setvar y
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
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint F x
  disjoint F y
  disjoint K f
  disjoint K i
  disjoint K n
  assert |- ( ( F e. Word RR /\ C e. RR+ ) -> H : ( 0 ..^ ( ( # ` F ) + 1 ) ) --> RR )

  proof
    cF
    cr
    cword
    #
    wcel
    #
    cC
    crp
    wcel
    #
    wa
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
    cr
    cc0
    cs1
    #
    cF
    cconcat
    co
    #
    cF
    @7
    cconcat
    co
    #
    cC
    cmul
    cofc
    co
    #
    cmin
    cof
    co
    #
    wf
    @6
    cr
    cH
    wf
    @3
    vx
    vy
    @6
    @6
    @6
    cmin
    cr
    cr
    cr
    @8
    @10
    cvv
    cvv
    vx
    cv
    #
    cr
    wcel
    vy
    cv
    #
    cr
    wcel
    wa
    #
    @12
    @13
    cmin
    co
    cr
    wcel
    @3
    @12
    @13
    resubcl
    adantl
    @3
    cc0
    @8
    chash
    cfv
    #
    cfzo
    co
    #
    cr
    @8
    wf
    #
    @6
    cr
    @8
    wf
    @3
    @8
    @0
    wcel
    #
    @17
    @3
    @7
    @0
    wcel
    #
    @1
    @18
    @3
    cc0
    cr
    @3
    0red
    s1cld
    #
    @1
    @2
    simpl
    #
    cr
    @7
    cF
    ccatcl
    syl2anc
    cr
    @8
    wrdf
    syl
    @3
    @16
    @6
    cr
    @8
    @3
    @15
    @5
    cc0
    cfzo
    @3
    @15
    c1
    @4
    caddc
    co
    #
    @5
    @3
    @15
    @7
    chash
    cfv
    #
    @4
    caddc
    co
    #
    @22
    @3
    @19
    @1
    @15
    @24
    wceq
    @20
    @21
    cr
    @7
    cF
    ccatlen
    syl2anc
    @23
    c1
    @4
    caddc
    cc0
    s1len
    #
    oveq1i
    syl6eq
    @3
    c1
    @4
    @3
    1cnd
    @3
    @4
    @3
    @1
    cF
    cfn
    wcel
    @4
    cn0
    wcel
    @21
    cr
    cF
    wrdfin
    cF
    hashcl
    3syl
    nn0cnd
    addcomd
    eqtrd
    oveq2d
    feq2d
    mpbid
    @3
    vx
    vy
    @6
    cC
    cmul
    cr
    cr
    cr
    @9
    cvv
    @14
    @12
    @13
    cmul
    co
    cr
    wcel
    @3
    @12
    @13
    remulcl
    adantl
    @3
    cc0
    @9
    chash
    cfv
    #
    cfzo
    co
    #
    cr
    @9
    wf
    #
    @6
    cr
    @9
    wf
    @3
    @9
    @0
    wcel
    #
    @28
    @1
    @2
    @19
    @29
    @20
    cr
    cF
    @7
    ccatcl
    syldan
    cr
    @9
    wrdf
    syl
    @3
    @27
    @6
    cr
    @9
    @3
    @26
    @5
    cc0
    cfzo
    @3
    @26
    @4
    @23
    caddc
    co
    #
    @5
    @1
    @2
    @19
    @26
    @30
    wceq
    @20
    cr
    cF
    @7
    ccatlen
    syldan
    @23
    c1
    @4
    caddc
    @25
    oveq2i
    syl6eq
    oveq2d
    feq2d
    mpbid
    @3
    cc0
    @5
    cfzo
    ovexd
    #
    @3
    cC
    @1
    @2
    simpr
    rpred
    ofcf
    @31
    @31
    @6
    inidm
    off
    @6
    cr
    cH
    @11
    signs.h
    feq1i
    sylibr
end
