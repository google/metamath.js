include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "cline2.mm"
include "co.mm"
include "clines2.mm"
include "cv.mm"
include "wrex.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "eqidd.mm"
include "neeq1.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "neeq2.mm"
include "oveq2.mm"
include "rspc2ev.mm"
include "syl112anc.mm"
include "fveq2.mm"
include "rexeqdv.mm"
include "rexeqbidv.mm"
include "rspcev.mm"
include "sylan2.mm"
include "ellines.mm"
include "sylibr.mm"
include "linerflx1.mm"
include "linerflx2.mm"
include "eleq2.mm"
include "syl12anc.mm"

theorem hilbert1.1
  let vx: setvar x
  let cP: class P
  let cQ: class Q
  let cN: class N
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q

  disjoint P x
  disjoint Q x
  disjoint N n
  disjoint n p
  disjoint N p
  disjoint n q
  disjoint N q
  disjoint P n
  disjoint P p
  disjoint p q
  disjoint P q
  disjoint Q n
  disjoint Q p
  disjoint Q q
  assert |- ( ( N e. NN /\ ( P e. ( EE ` N ) /\ Q e. ( EE ` N ) /\ P =/= Q ) ) -> E. x e. LinesEE ( P e. x /\ Q e. x ) )

  proof
    cN
    cn
    wcel
    #
    cP
    cN
    cee
    cfv
    #
    wcel
    #
    cQ
    @1
    wcel
    #
    cP
    cQ
    wne
    #
    w3a
    #
    wa
    #
    cP
    cQ
    cline2
    co
    #
    clines2
    wcel
    #
    cP
    @7
    wcel
    #
    cQ
    @7
    wcel
    #
    cP
    vx
    cv
    #
    wcel
    #
    cQ
    @11
    wcel
    #
    wa
    #
    vx
    clines2
    wrex
    @6
    vp
    cv
    #
    vq
    cv
    #
    wne
    #
    @7
    @15
    @16
    cline2
    co
    #
    wceq
    #
    wa
    #
    vq
    vn
    cv
    #
    cee
    cfv
    #
    wrex
    #
    vp
    @22
    wrex
    #
    vn
    cn
    wrex
    #
    @8
    @5
    @0
    @20
    vq
    @1
    wrex
    #
    vp
    @1
    wrex
    #
    @25
    @5
    @2
    @3
    @4
    @7
    @7
    wceq
    #
    @27
    @2
    @3
    @4
    simp1
    @2
    @3
    @4
    simp2
    @2
    @3
    @4
    simp3
    @5
    @7
    eqidd
    @20
    @4
    @28
    wa
    cP
    @16
    wne
    #
    @7
    cP
    @16
    cline2
    co
    #
    wceq
    #
    wa
    vp
    vq
    cP
    cQ
    @1
    @1
    @15
    cP
    wceq
    #
    @17
    @29
    @19
    @31
    @15
    cP
    @16
    neeq1
    @32
    @18
    @30
    @7
    @15
    cP
    @16
    cline2
    oveq1
    eqeq2d
    anbi12d
    @16
    cQ
    wceq
    #
    @29
    @4
    @31
    @28
    @16
    cQ
    cP
    neeq2
    @33
    @30
    @7
    @7
    @16
    cQ
    cP
    cline2
    oveq2
    eqeq2d
    anbi12d
    rspc2ev
    syl112anc
    @24
    @27
    vn
    cN
    cn
    @21
    cN
    wceq
    #
    @23
    @26
    vp
    @22
    @1
    @21
    cN
    cee
    fveq2
    #
    @34
    @20
    vq
    @22
    @1
    @35
    rexeqdv
    rexeqbidv
    rspcev
    sylan2
    @7
    vn
    vq
    vp
    ellines
    sylibr
    cP
    cQ
    cN
    linerflx1
    cP
    cQ
    cN
    linerflx2
    @14
    @9
    @10
    wa
    vx
    @7
    clines2
    @11
    @7
    wceq
    @12
    @9
    @13
    @10
    @11
    @7
    cP
    eleq2
    @11
    @7
    cQ
    eleq2
    anbi12d
    rspcev
    syl12anc
end
