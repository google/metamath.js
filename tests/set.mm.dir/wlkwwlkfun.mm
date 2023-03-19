include "cupgr.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "cv.mm"
include "c2nd.mm"
include "cfv.mm"
include "wa.mm"
include "cwwlksn.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "cwlks.mm"
include "c1st.mm"
include "chash.mm"
include "weq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "fveq1d.mm"
include "anbi12d.mm"
include "elrab2.mm"
include "simp1.mm"
include "simpl.mm"
include "anim12i.mm"
include "simp3.mm"
include "simprl.mm"
include "wlknewwlksn.mm"
include "syl2anc.mm"
include "simprrr.mm"
include "jca.mm"
include "sylan2b.mm"
include "fveq1.mm"
include "sylibr.mm"
include "fmptd.mm"

theorem wlkwwlkfun
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
  assert |- ( ( G e. UPGraph /\ P e. V /\ N e. NN0 ) -> F : T --> W )

  proof
    cG
    cupgr
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
    vt
    cT
    vt
    cv
    #
    c2nd
    cfv
    #
    cW
    cF
    @3
    @4
    cT
    wcel
    #
    wa
    @5
    cN
    cG
    cwwlksn
    co
    #
    wcel
    #
    cc0
    @5
    cfv
    #
    cP
    wceq
    #
    wa
    #
    @5
    cW
    wcel
    @6
    @3
    @4
    cG
    cwlks
    cfv
    #
    wcel
    #
    @4
    c1st
    cfv
    #
    chash
    cfv
    #
    cN
    wceq
    #
    @10
    wa
    #
    wa
    #
    @11
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
    @19
    c2nd
    cfv
    #
    cfv
    #
    cP
    wceq
    #
    wa
    @17
    vp
    @4
    @12
    cT
    vp
    vt
    weq
    #
    @22
    @16
    @25
    @10
    @26
    @21
    @15
    cN
    @26
    @20
    @14
    chash
    @19
    @4
    c1st
    fveq2
    fveq2d
    eqeq1d
    @26
    @24
    @9
    cP
    @26
    cc0
    @23
    @5
    @19
    @4
    c2nd
    fveq2
    fveq1d
    eqeq1d
    anbi12d
    wlkwwlkbij.t
    elrab2
    @3
    @18
    wa
    #
    @8
    @10
    @27
    @0
    @13
    wa
    @2
    @16
    wa
    @8
    @3
    @0
    @18
    @13
    @0
    @1
    @2
    simp1
    @13
    @17
    simpl
    anim12i
    @3
    @2
    @18
    @16
    @0
    @1
    @2
    simp3
    @13
    @16
    @10
    simprl
    anim12i
    cG
    cN
    @4
    wlknewwlksn
    syl2anc
    @3
    @13
    @16
    @10
    simprrr
    jca
    sylan2b
    cc0
    vw
    cv
    #
    cfv
    #
    cP
    wceq
    @10
    vw
    @5
    @7
    cW
    @28
    @5
    wceq
    @29
    @9
    cP
    cc0
    @28
    @5
    fveq1
    eqeq1d
    wlkwwlkbij.w
    elrab2
    sylibr
    wlkwwlkbij.f
    fmptd
end
