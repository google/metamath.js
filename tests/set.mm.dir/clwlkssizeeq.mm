include "cfusgr.mm"
include "wcel.mm"
include "cprime.mm"
include "wa.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "chash.mm"
include "wceq.mm"
include "cclwlks.mm"
include "crab.mm"
include "cclwwlkn.mm"
include "co.mm"
include "cvv.mm"
include "c2nd.mm"
include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "cmpt.mm"
include "fvex.mm"
include "rabex.mm"
include "a1i.mm"
include "eqid.mm"
include "weq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "cbvrabv.mm"
include "opeq2d.mm"
include "oveq12d.mm"
include "cbvmptv.mm"
include "clwlksf1oclwwlk.mm"
include "hasheqf1od.mm"
include "eqcomd.mm"

theorem clwlkssizeeq
  let cG: class G
  let cN: class N
  let vc: setvar c
  let vu: setvar u
  let vw: setvar w

  disjoint G c
  disjoint N c
  disjoint G u
  disjoint G w
  disjoint c u
  disjoint c w
  disjoint u w
  disjoint N u
  disjoint N w
  assert |- ( ( G e. FinUSGraph /\ N e. Prime ) -> ( # ` ( N ClWWalksN G ) ) = ( # ` { c e. ( ClWalks ` G ) | ( # ` ( 1st ` c ) ) = N } ) )

  proof
    cG
    cfusgr
    wcel
    cN
    cprime
    wcel
    wa
    #
    vc
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
    vc
    cG
    cclwlks
    cfv
    #
    crab
    #
    chash
    cfv
    cN
    cG
    cclwwlkn
    co
    #
    chash
    cfv
    @0
    @6
    @7
    cvv
    vu
    @6
    vu
    cv
    #
    c2nd
    cfv
    #
    cc0
    @8
    c1st
    cfv
    #
    chash
    cfv
    #
    cop
    #
    csubstr
    co
    #
    cmpt
    #
    @6
    cvv
    wcel
    @0
    @4
    vc
    @5
    cG
    cclwlks
    fvex
    rabex
    a1i
    vw
    cv
    #
    c1st
    cfv
    #
    @15
    c2nd
    cfv
    #
    @6
    @14
    cG
    cN
    vw
    @16
    eqid
    @17
    eqid
    @4
    @16
    chash
    cfv
    #
    cN
    wceq
    vc
    vw
    @5
    vc
    vw
    weq
    #
    @3
    @18
    cN
    @19
    @2
    @16
    chash
    @1
    @15
    c1st
    fveq2
    fveq2d
    eqeq1d
    cbvrabv
    vu
    vw
    @6
    @13
    @17
    cc0
    @18
    cop
    #
    csubstr
    co
    vu
    vw
    weq
    #
    @9
    @17
    @12
    @20
    csubstr
    @8
    @15
    c2nd
    fveq2
    @21
    @11
    @18
    cc0
    @21
    @10
    @16
    chash
    @8
    @15
    c1st
    fveq2
    fveq2d
    opeq2d
    oveq12d
    cbvmptv
    clwlksf1oclwwlk
    hasheqf1od
    eqcomd
end
