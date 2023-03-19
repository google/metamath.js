include "wcel.mm"
include "cvv.mm"
include "chdma1.mm"
include "cfv.mm"
include "cv.mm"
include "cxp.mm"
include "c2nd.mm"
include "c0g.mm"
include "wceq.mm"
include "csn.mm"
include "c1st.mm"
include "csg.mm"
include "co.mm"
include "wa.mm"
include "crio.mm"
include "cif.mm"
include "cmpt.mm"
include "cmpd.mm"
include "wsbc.mm"
include "clspn.mm"
include "cbs.mm"
include "clcd.mm"
include "cdvh.mm"
include "cab.mm"
include "elex.mm"
include "clh.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "sbceq1d.mm"
include "sbcbidv.mm"
include "sbceqbid.mm"
include "abbidv.mm"
include "mpteq12dv.mm"
include "df-hdmap1.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem hdmap1ffval
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vh: setvar h
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let cH: class H
  let cK: class K
  let cX: class X
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let vk: setvar k
  assume hdmap1val.h: |- H = ( LHyp ` K )

  disjoint H w
  disjoint a c
  disjoint a d
  disjoint a j
  disjoint a m
  disjoint a n
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint K a
  disjoint c d
  disjoint c j
  disjoint c m
  disjoint c n
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint K c
  disjoint d j
  disjoint d m
  disjoint d n
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint K d
  disjoint j m
  disjoint j n
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint K j
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint K m
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint K n
  disjoint u v
  disjoint u w
  disjoint K u
  disjoint v w
  disjoint K v
  disjoint K w
  disjoint a h
  disjoint a x
  disjoint c h
  disjoint c x
  disjoint d h
  disjoint d x
  disjoint h j
  disjoint h m
  disjoint h n
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h x
  disjoint j x
  disjoint m x
  disjoint n x
  disjoint u x
  disjoint v x
  disjoint w x
  disjoint k w
  disjoint H k
  disjoint a k
  disjoint c k
  disjoint d k
  disjoint j k
  disjoint k m
  disjoint k n
  disjoint k u
  disjoint k v
  disjoint K k
  disjoint h k
  disjoint k x
  assert |- ( K e. X -> ( HDMap1 ` K ) = ( w e. H |-> { a | [. ( ( DVecH ` K ) ` w ) / u ]. [. ( Base ` u ) / v ]. [. ( LSpan ` u ) / n ]. [. ( ( LCDual ` K ) ` w ) / c ]. [. ( Base ` c ) / d ]. [. ( LSpan ` c ) / j ]. [. ( ( mapd ` K ) ` w ) / m ]. a e. ( x e. ( ( v X. d ) X. v ) |-> if ( ( 2nd ` x ) = ( 0g ` u ) , ( 0g ` c ) , ( iota_ h e. d ( ( m ` ( n ` { ( 2nd ` x ) } ) ) = ( j ` { h } ) /\ ( m ` ( n ` { ( ( 1st ` ( 1st ` x ) ) ( -g ` u ) ( 2nd ` x ) ) } ) ) = ( j ` { ( ( 2nd ` ( 1st ` x ) ) ( -g ` c ) h ) } ) ) ) ) ) } ) )

  proof
    cK
    cX
    wcel
    cK
    cvv
    wcel
    cK
    chdma1
    cfv
    vw
    cH
    va
    cv
    vx
    vv
    cv
    #
    vd
    cv
    #
    cxp
    @0
    cxp
    vx
    cv
    #
    c2nd
    cfv
    #
    vu
    cv
    #
    c0g
    cfv
    wceq
    vc
    cv
    #
    c0g
    cfv
    @3
    csn
    vn
    cv
    #
    cfv
    vm
    cv
    #
    cfv
    vh
    cv
    #
    csn
    vj
    cv
    #
    cfv
    wceq
    @2
    c1st
    cfv
    #
    c1st
    cfv
    @3
    @4
    csg
    cfv
    co
    csn
    @6
    cfv
    @7
    cfv
    @10
    c2nd
    cfv
    @8
    @5
    csg
    cfv
    co
    csn
    @9
    cfv
    wceq
    wa
    vh
    @1
    crio
    cif
    cmpt
    wcel
    #
    vm
    vw
    cv
    #
    cK
    cmpd
    cfv
    #
    cfv
    #
    wsbc
    #
    vj
    @5
    clspn
    cfv
    #
    wsbc
    #
    vd
    @5
    cbs
    cfv
    #
    wsbc
    #
    vc
    @12
    cK
    clcd
    cfv
    #
    cfv
    #
    wsbc
    #
    vn
    @4
    clspn
    cfv
    #
    wsbc
    #
    vv
    @4
    cbs
    cfv
    #
    wsbc
    #
    vu
    @12
    cK
    cdvh
    cfv
    #
    cfv
    #
    wsbc
    #
    va
    cab
    #
    cmpt
    #
    wceq
    cK
    cX
    elex
    vk
    cK
    vw
    vk
    cv
    #
    clh
    cfv
    #
    @11
    vm
    @12
    @32
    cmpd
    cfv
    #
    cfv
    #
    wsbc
    #
    vj
    @16
    wsbc
    #
    vd
    @18
    wsbc
    #
    vc
    @12
    @32
    clcd
    cfv
    #
    cfv
    #
    wsbc
    #
    vn
    @23
    wsbc
    #
    vv
    @25
    wsbc
    #
    vu
    @12
    @32
    cdvh
    cfv
    #
    cfv
    #
    wsbc
    #
    va
    cab
    #
    cmpt
    @31
    cvv
    chdma1
    @32
    cK
    wceq
    #
    vw
    @33
    @47
    cH
    @30
    @48
    @33
    cK
    clh
    cfv
    #
    cH
    @32
    cK
    clh
    fveq2
    hdmap1val.h
    syl6eqr
    @48
    @46
    @29
    va
    @48
    @43
    @26
    vu
    @45
    @28
    @48
    @12
    @44
    @27
    @32
    cK
    cdvh
    fveq2
    fveq1d
    @48
    @42
    @24
    vv
    @25
    @48
    @41
    @22
    vn
    @23
    @48
    @38
    @19
    vc
    @40
    @21
    @48
    @12
    @39
    @20
    @32
    cK
    clcd
    fveq2
    fveq1d
    @48
    @37
    @17
    vd
    @18
    @48
    @36
    @15
    vj
    @16
    @48
    @11
    vm
    @35
    @14
    @48
    @12
    @34
    @13
    @32
    cK
    cmpd
    fveq2
    fveq1d
    sbceq1d
    sbcbidv
    sbcbidv
    sbceqbid
    sbcbidv
    sbcbidv
    sbceqbid
    abbidv
    mpteq12dv
    vx
    vw
    vv
    vu
    vh
    vj
    vk
    vm
    vn
    va
    vc
    vd
    df-hdmap1
    vw
    cH
    @30
    cH
    @49
    cvv
    hdmap1val.h
    cK
    clh
    fvex
    eqeltri
    mptex
    fvmpt
    syl
end
