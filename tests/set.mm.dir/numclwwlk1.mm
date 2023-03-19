include "cfn.mm"
include "wcel.mm"
include "crusgr.mm"
include "wbr.mm"
include "wa.mm"
include "c3.mm"
include "cuz.mm"
include "cfv.mm"
include "co.mm"
include "chash.mm"
include "cnbgr.mm"
include "cxp.mm"
include "cmul.mm"
include "cvv.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "wceq.mm"
include "ovex.mm"
include "cusgr.mm"
include "rusgrusgr.mm"
include "ad2antlr.mm"
include "simprl.mm"
include "simprr.mm"
include "numclwlk1lem2.mm"
include "syl3anc.mm"
include "hasheqf1oi.mm"
include "mpsyl.mm"
include "cvtx.mm"
include "c2.mm"
include "cmin.mm"
include "cclwwlknon.mm"
include "eqid.mm"
include "clwwlknonfin.mm"
include "eleq1i.mm"
include "3imtr4i.mm"
include "adantr.mm"
include "cedg.mm"
include "cfusgr.mm"
include "finrusgrfusgr.mm"
include "ancoms.mm"
include "fusgrfis.mm"
include "syl.mm"
include "nbusgrfi.mm"
include "hashxp.mm"
include "syl2anc.mm"
include "wi.mm"
include "cxnn0.mm"
include "wral.mm"
include "w3a.mm"
include "rusgrpropnb.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "rspccv.mm"
include "3ad2ant3.mm"
include "adantl.mm"
include "com12.mm"
include "impcom.mm"
include "oveq2d.mm"
include "cn0.mm"
include "cc.mm"
include "hashcl.mm"
include "nn0cn.mm"
include "3syl.mm"
include "c0.mm"
include "wne.mm"
include "simplr.mm"
include "ne0i.mm"
include "frusgrnn0.mm"
include "nn0cnd.mm"
include "mulcomd.mm"
include "eqtrd.mm"
include "3eqtrd.mm"

theorem numclwwlk1
  let vw: setvar w
  let vv: setvar v
  let cC: class C
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cK: class K
  let cN: class N
  let cV: class V
  let cX: class X
  let cW: class W
  let vi: setvar i
  let cY: class Y
  let vu: setvar u
  let vf: setvar f
  let vx: setvar x
  assume extwwlkfab.v: |- V = ( Vtx ` G )
  assume extwwlkfab.c: |- C = ( v e. V , n e. ( ZZ>= ` 2 ) |-> { w e. ( n ClWWalksN G ) | ( ( w ` 0 ) = v /\ ( w ` ( n - 2 ) ) = ( w ` 0 ) ) } )
  assume extwwlkfab.f: |- F = ( X ( ClWWalksNOn ` G ) ( N - 2 ) )

  disjoint G n
  disjoint G v
  disjoint G w
  disjoint n v
  disjoint n w
  disjoint v w
  disjoint V n
  disjoint V v
  disjoint V w
  disjoint X n
  disjoint X v
  disjoint X w
  disjoint N n
  disjoint N v
  disjoint N w
  disjoint F w
  disjoint C w
  disjoint W w
  disjoint G i
  disjoint W i
  disjoint Y w
  disjoint C u
  disjoint F u
  disjoint G u
  disjoint u w
  disjoint N u
  disjoint V u
  disjoint X u
  disjoint C f
  disjoint f w
  disjoint F f
  disjoint G f
  disjoint N f
  disjoint X f
  disjoint G x
  disjoint K x
  disjoint V x
  disjoint X x
  assert |- ( ( ( V e. Fin /\ G RegUSGraph K ) /\ ( X e. V /\ N e. ( ZZ>= ` 3 ) ) ) -> ( # ` ( X C N ) ) = ( K x. ( # ` F ) ) )

  proof
    cV
    cfn
    wcel
    #
    cG
    cK
    crusgr
    wbr
    #
    wa
    #
    cX
    cV
    wcel
    #
    cN
    c3
    cuz
    cfv
    wcel
    #
    wa
    #
    wa
    #
    cX
    cN
    cC
    co
    #
    chash
    cfv
    #
    cF
    cG
    cX
    cnbgr
    co
    #
    cxp
    #
    chash
    cfv
    #
    cF
    chash
    cfv
    #
    @9
    chash
    cfv
    #
    cmul
    co
    #
    cK
    @12
    cmul
    co
    #
    @7
    cvv
    wcel
    @6
    @7
    @10
    vf
    cv
    wf1o
    vf
    wex
    #
    @8
    @11
    wceq
    cX
    cN
    cC
    ovex
    @6
    cG
    cusgr
    wcel
    #
    @3
    @4
    @16
    @1
    @17
    @0
    @5
    cG
    cK
    rusgrusgr
    ad2antlr
    #
    @2
    @3
    @4
    simprl
    #
    @2
    @3
    @4
    simprr
    vw
    vv
    cC
    vf
    vn
    cF
    cG
    cN
    cV
    cX
    extwwlkfab.v
    extwwlkfab.c
    extwwlkfab.f
    numclwlk1lem2
    syl3anc
    @7
    @10
    vf
    cvv
    hasheqf1oi
    mpsyl
    @6
    cF
    cfn
    wcel
    #
    @9
    cfn
    wcel
    #
    @11
    @14
    wceq
    @2
    @20
    @5
    @0
    @20
    @1
    cG
    cvtx
    cfv
    #
    cfn
    wcel
    cX
    cN
    c2
    cmin
    co
    #
    cG
    cclwwlknon
    cfv
    co
    #
    cfn
    wcel
    @0
    @20
    cG
    @23
    @22
    cX
    @22
    eqid
    clwwlknonfin
    cV
    @22
    cfn
    extwwlkfab.v
    eleq1i
    cF
    @24
    cfn
    extwwlkfab.f
    eleq1i
    3imtr4i
    adantr
    adantr
    #
    @6
    @17
    cG
    cedg
    cfv
    #
    cfn
    wcel
    #
    @3
    @21
    @18
    @2
    @27
    @5
    @2
    cG
    cfusgr
    wcel
    #
    @27
    @1
    @0
    @28
    cG
    cK
    cV
    extwwlkfab.v
    finrusgrfusgr
    ancoms
    #
    cG
    fusgrfis
    syl
    adantr
    @19
    cX
    @26
    cG
    cV
    extwwlkfab.v
    @26
    eqid
    nbusgrfi
    syl3anc
    cF
    @9
    hashxp
    syl2anc
    @6
    @14
    @12
    cK
    cmul
    co
    @15
    @6
    @13
    cK
    @12
    cmul
    @5
    @2
    @13
    cK
    wceq
    #
    @3
    @2
    @30
    wi
    @4
    @2
    @3
    @30
    @1
    @3
    @30
    wi
    #
    @0
    @1
    @17
    cK
    cxnn0
    wcel
    #
    cG
    vx
    cv
    #
    cnbgr
    co
    #
    chash
    cfv
    #
    cK
    wceq
    #
    vx
    cV
    wral
    #
    w3a
    @31
    vx
    cG
    cK
    cV
    extwwlkfab.v
    rusgrpropnb
    @37
    @17
    @31
    @32
    @36
    @30
    vx
    cX
    cV
    @33
    cX
    wceq
    #
    @35
    @13
    cK
    @38
    @34
    @9
    chash
    @33
    cX
    cG
    cnbgr
    oveq2
    fveq2d
    eqeq1d
    rspccv
    3ad2ant3
    syl
    adantl
    com12
    adantr
    impcom
    oveq2d
    @6
    @12
    cK
    @6
    @20
    @12
    cn0
    wcel
    @12
    cc
    wcel
    @25
    cF
    hashcl
    @12
    nn0cn
    3syl
    @6
    cK
    @6
    @28
    @1
    cV
    c0
    wne
    #
    cK
    cn0
    wcel
    @2
    @28
    @5
    @29
    adantr
    @0
    @1
    @5
    simplr
    @5
    @39
    @2
    @3
    @39
    @4
    cV
    cX
    ne0i
    adantr
    adantl
    cG
    cK
    cV
    extwwlkfab.v
    frusgrnn0
    syl3anc
    nn0cnd
    mulcomd
    eqtrd
    3eqtrd
end
