include "cuspgr.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wf1.mm"
include "cupgr.mm"
include "uspgrupgr.mm"
include "wlkwwlkfun.mm"
include "syl3an1.mm"
include "wa.mm"
include "c2nd.mm"
include "wb.mm"
include "fveq2.mm"
include "fvex.mm"
include "fvmpt.mm"
include "eqeqan12d.mm"
include "adantl.mm"
include "cwlks.mm"
include "c1st.mm"
include "chash.mm"
include "cc0.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "fveq1d.mm"
include "anbi12d.mm"
include "elrab2.mm"
include "anbi12i.mm"
include "3simpb.mm"
include "adantr.mm"
include "simpl.mm"
include "anim2i.mm"
include "uspgr2wlkeq2.mm"
include "syl3anc.mm"
include "sylan2b.mm"
include "sylbid.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"

theorem wlkwwlkinj
  let vw: setvar w
  let vt: setvar t
  let cP: class P
  let cT: class T
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let vp: setvar p
  let vv: setvar v
  assume wlkwwlkbij.t: |- T = { p e. ( Walks ` G ) | ( ( # ` ( 1st ` p ) ) = N /\ ( ( 2nd ` p ) ` 0 ) = P ) }
  assume wlkwwlkbij.w: |- W = { w e. ( N WWalksN G ) | ( w ` 0 ) = P }
  assume wlkwwlkbij.f: |- F = ( t e. T |-> ( 2nd ` t ) )

  disjoint G p
  disjoint G t
  disjoint G w
  disjoint p t
  disjoint p w
  disjoint t w
  disjoint N p
  disjoint N t
  disjoint N w
  disjoint P p
  disjoint P t
  disjoint P w
  disjoint T t
  disjoint T w
  disjoint V t
  disjoint W t
  disjoint F w
  disjoint V w
  disjoint F v
  disjoint v w
  disjoint G v
  disjoint p v
  disjoint N v
  disjoint P v
  disjoint T v
  disjoint t v
  disjoint V v
  assert |- ( ( G e. USPGraph /\ P e. V /\ N e. NN0 ) -> F : T -1-1-> W )

  proof
    cG
    cuspgr
    wcel
    #
    cP
    cV
    wcel
    #
    cN
    cn0
    wcel
    #
    w3a
    #
    cT
    cW
    cF
    wf
    #
    vv
    cv
    #
    cF
    cfv
    #
    vw
    cv
    #
    cF
    cfv
    #
    wceq
    #
    @5
    @7
    wceq
    #
    wi
    #
    vw
    cT
    wral
    vv
    cT
    wral
    cT
    cW
    cF
    wf1
    @0
    cG
    cupgr
    wcel
    @1
    @2
    @4
    cG
    uspgrupgr
    vw
    vt
    cP
    cT
    cF
    cG
    cN
    cV
    cW
    vp
    wlkwwlkbij.t
    wlkwwlkbij.w
    wlkwwlkbij.f
    wlkwwlkfun
    syl3an1
    @3
    @11
    vv
    vw
    cT
    cT
    @3
    @5
    cT
    wcel
    #
    @7
    cT
    wcel
    #
    wa
    #
    wa
    @9
    @5
    c2nd
    cfv
    #
    @7
    c2nd
    cfv
    #
    wceq
    #
    @10
    @14
    @9
    @17
    wb
    @3
    @12
    @13
    @6
    @15
    @8
    @16
    vt
    @5
    vt
    cv
    #
    c2nd
    cfv
    #
    @15
    cT
    cF
    @18
    @5
    c2nd
    fveq2
    wlkwwlkbij.f
    @5
    c2nd
    fvex
    fvmpt
    vt
    @7
    @19
    @16
    cT
    cF
    @18
    @7
    c2nd
    fveq2
    wlkwwlkbij.f
    @7
    c2nd
    fvex
    fvmpt
    eqeqan12d
    adantl
    @14
    @3
    @5
    cG
    cwlks
    cfv
    #
    wcel
    #
    @5
    c1st
    cfv
    #
    chash
    cfv
    #
    cN
    wceq
    #
    cc0
    @15
    cfv
    #
    cP
    wceq
    #
    wa
    #
    wa
    #
    @7
    @20
    wcel
    #
    @7
    c1st
    cfv
    #
    chash
    cfv
    #
    cN
    wceq
    #
    cc0
    @16
    cfv
    #
    cP
    wceq
    #
    wa
    #
    wa
    #
    wa
    #
    @17
    @10
    wi
    #
    @12
    @28
    @13
    @36
    vp
    cv
    #
    c1st
    cfv
    #
    chash
    cfv
    #
    cN
    wceq
    #
    cc0
    @39
    c2nd
    cfv
    #
    cfv
    #
    cP
    wceq
    #
    wa
    #
    @27
    vp
    @5
    @20
    cT
    @39
    @5
    wceq
    #
    @42
    @24
    @45
    @26
    @47
    @41
    @23
    cN
    @47
    @40
    @22
    chash
    @39
    @5
    c1st
    fveq2
    fveq2d
    eqeq1d
    @47
    @44
    @25
    cP
    @47
    cc0
    @43
    @15
    @39
    @5
    c2nd
    fveq2
    fveq1d
    eqeq1d
    anbi12d
    wlkwwlkbij.t
    elrab2
    @46
    @35
    vp
    @7
    @20
    cT
    @39
    @7
    wceq
    #
    @42
    @32
    @45
    @34
    @48
    @41
    @31
    cN
    @48
    @40
    @30
    chash
    @39
    @7
    c1st
    fveq2
    fveq2d
    eqeq1d
    @48
    @44
    @33
    cP
    @48
    cc0
    @43
    @16
    @39
    @7
    c2nd
    fveq2
    fveq1d
    eqeq1d
    anbi12d
    wlkwwlkbij.t
    elrab2
    anbi12i
    @3
    @37
    wa
    @0
    @2
    wa
    #
    @21
    @24
    wa
    #
    @29
    @32
    wa
    #
    @38
    @3
    @49
    @37
    @0
    @1
    @2
    3simpb
    adantr
    @37
    @50
    @3
    @28
    @50
    @36
    @27
    @24
    @21
    @24
    @26
    simpl
    anim2i
    adantr
    adantl
    @37
    @51
    @3
    @36
    @51
    @28
    @35
    @32
    @29
    @32
    @34
    simpl
    anim2i
    adantl
    adantl
    @5
    @7
    cG
    cN
    uspgr2wlkeq2
    syl3anc
    sylan2b
    sylbid
    ralrimivva
    vv
    vw
    cT
    cW
    cF
    dff13
    sylanbrc
end
