include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "crp.mm"
include "cv.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "wf.mm"
include "cc.mm"
include "wss.mm"
include "wb.mm"
include "cncfrss.mm"
include "cncfrss2.mm"
include "elcncf2.mm"
include "syl2anc.mm"
include "ibi.mm"
include "simprd.mm"
include "wceq.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "imbi12d.mm"
include "rexralbidv.mm"
include "breq2.mm"
include "imbi2d.mm"
include "rspc2v.mm"
include "mpan9.mm"
include "3impb.mm"

theorem cncfi
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y

  disjoint w z
  disjoint A w
  disjoint A z
  disjoint C w
  disjoint C z
  disjoint F w
  disjoint F z
  disjoint R w
  disjoint R z
  disjoint B w
  disjoint B z
  disjoint a b
  disjoint a f
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint b f
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint w x
  disjoint w y
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint C x
  disjoint C y
  disjoint F f
  disjoint F x
  disjoint F y
  disjoint R y
  disjoint B a
  disjoint B b
  disjoint B f
  disjoint B x
  disjoint B y
  assert |- ( ( F e. ( A -cn-> B ) /\ C e. A /\ R e. RR+ ) -> E. z e. RR+ A. w e. A ( ( abs ` ( w - C ) ) < z -> ( abs ` ( ( F ` w ) - ( F ` C ) ) ) < R ) )

  proof
    cF
    cA
    cB
    ccncf
    co
    wcel
    #
    cC
    cA
    wcel
    #
    cR
    crp
    wcel
    #
    vw
    cv
    #
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    vz
    cv
    #
    clt
    wbr
    #
    @3
    cF
    cfv
    #
    cC
    cF
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cR
    clt
    wbr
    #
    wi
    #
    vw
    cA
    wral
    vz
    crp
    wrex
    #
    @0
    @3
    vx
    cv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @6
    clt
    wbr
    #
    @8
    @15
    cF
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    vy
    cv
    #
    clt
    wbr
    #
    wi
    #
    vw
    cA
    wral
    vz
    crp
    wrex
    #
    vy
    crp
    wral
    vx
    cA
    wral
    #
    @1
    @2
    wa
    @14
    @0
    cA
    cB
    cF
    wf
    #
    @26
    @0
    @27
    @26
    wa
    #
    @0
    cA
    cc
    wss
    cB
    cc
    wss
    @0
    @28
    wb
    cA
    cB
    cF
    cncfrss
    cA
    cB
    cF
    cncfrss2
    vx
    vy
    vz
    vw
    cA
    cB
    cF
    elcncf2
    syl2anc
    ibi
    simprd
    @25
    @14
    @7
    @11
    @22
    clt
    wbr
    #
    wi
    #
    vw
    cA
    wral
    vz
    crp
    wrex
    vx
    vy
    cC
    cR
    cA
    crp
    @15
    cC
    wceq
    #
    @24
    @30
    vz
    vw
    crp
    cA
    @31
    @18
    @7
    @23
    @29
    @31
    @17
    @5
    @6
    clt
    @31
    @16
    @4
    cabs
    @15
    cC
    @3
    cmin
    oveq2
    fveq2d
    breq1d
    @31
    @21
    @11
    @22
    clt
    @31
    @20
    @10
    cabs
    @31
    @19
    @9
    @8
    cmin
    @15
    cC
    cF
    fveq2
    oveq2d
    fveq2d
    breq1d
    imbi12d
    rexralbidv
    @22
    cR
    wceq
    #
    @30
    @13
    vz
    vw
    crp
    cA
    @32
    @29
    @12
    @7
    @22
    cR
    @11
    clt
    breq2
    imbi2d
    rexralbidv
    rspc2v
    mpan9
    3impb
end
