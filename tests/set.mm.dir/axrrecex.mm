include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "wrex.mm"
include "c0r.mm"
include "cop.mm"
include "wi.mm"
include "cnr.mm"
include "wa.mm"
include "wex.mm"
include "elreal.mm"
include "df-rex.mm"
include "bitri.mm"
include "neeq1.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "df-0.mm"
include "eqeq2i.mm"
include "vex.mm"
include "eqresr.mm"
include "necon3bii.mm"
include "cmr.mm"
include "c1r.mm"
include "recexsr.mm"
include "ex.mm"
include "opelreal.mm"
include "anbi1i.mm"
include "mulresr.mm"
include "df-1.mm"
include "ovex.mm"
include "syl6bb.mm"
include "pm5.32da.mm"
include "syl5bb.mm"
include "oveq2.mm"
include "rspcev.mm"
include "syl6bir.mm"
include "expd.mm"
include "rexlimdv.mm"
include "syld.mm"
include "syl5bi.mm"
include "gencl.mm"
include "imp.mm"

theorem axrrecex
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint x z
  disjoint y z
  assert |- ( ( A e. RR /\ A =/= 0 ) -> E. x e. RR ( A x. x ) = 1 )

  proof
    cA
    cr
    wcel
    #
    cA
    cc0
    wne
    #
    cA
    vx
    cv
    #
    cmul
    co
    #
    c1
    wceq
    #
    vx
    cr
    wrex
    #
    vy
    cv
    #
    c0r
    cop
    #
    cc0
    wne
    #
    @7
    @2
    cmul
    co
    #
    c1
    wceq
    #
    vx
    cr
    wrex
    #
    wi
    @1
    @5
    wi
    @6
    cnr
    wcel
    #
    @0
    vy
    @7
    cA
    @0
    @7
    cA
    wceq
    #
    vy
    cnr
    wrex
    @12
    @13
    wa
    vy
    wex
    vy
    cA
    elreal
    @13
    vy
    cnr
    df-rex
    bitri
    @13
    @8
    @1
    @11
    @5
    @7
    cA
    cc0
    neeq1
    @13
    @10
    @4
    vx
    cr
    @13
    @9
    @3
    c1
    @7
    cA
    @2
    cmul
    oveq1
    eqeq1d
    rexbidv
    imbi12d
    @8
    @6
    c0r
    wne
    #
    @12
    @11
    @7
    cc0
    @6
    c0r
    @7
    cc0
    wceq
    @7
    c0r
    c0r
    cop
    #
    wceq
    @6
    c0r
    wceq
    cc0
    @15
    @7
    df-0
    eqeq2i
    @6
    c0r
    vy
    vex
    eqresr
    bitri
    necon3bii
    @12
    @14
    @6
    vz
    cv
    #
    cmr
    co
    #
    c1r
    wceq
    #
    vz
    cnr
    wrex
    #
    @11
    @12
    @14
    @19
    vz
    @6
    recexsr
    ex
    @12
    @18
    @11
    vz
    cnr
    @12
    @16
    cnr
    wcel
    #
    @18
    @11
    @12
    @20
    @18
    wa
    #
    @16
    c0r
    cop
    #
    cr
    wcel
    #
    @7
    @22
    cmul
    co
    #
    c1
    wceq
    #
    wa
    #
    @11
    @26
    @20
    @25
    wa
    @12
    @21
    @23
    @20
    @25
    @16
    opelreal
    anbi1i
    @12
    @20
    @25
    @18
    @12
    @20
    wa
    #
    @25
    @17
    c0r
    cop
    #
    c1
    wceq
    #
    @18
    @27
    @24
    @28
    c1
    @6
    @16
    mulresr
    eqeq1d
    @29
    @28
    c1r
    c0r
    cop
    #
    wceq
    @18
    c1
    @30
    @28
    df-1
    eqeq2i
    @17
    c1r
    @6
    @16
    cmr
    ovex
    eqresr
    bitri
    syl6bb
    pm5.32da
    syl5bb
    @10
    @25
    vx
    @22
    cr
    @2
    @22
    wceq
    @9
    @24
    c1
    @2
    @22
    @7
    cmul
    oveq2
    eqeq1d
    rspcev
    syl6bir
    expd
    rexlimdv
    syld
    syl5bi
    gencl
    imp
end
