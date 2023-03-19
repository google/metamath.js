include "chlt.mm"
include "wcel.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wbr.mm"
include "w3a.mm"
include "wrex.mm"
include "wi.mm"
include "wn.mm"
include "wa.mm"
include "wral.mm"
include "coml.mm"
include "ccla.mm"
include "cal.mm"
include "cp0.mm"
include "cfv.mm"
include "cplt.mm"
include "cp1.mm"
include "eqid.mm"
include "ishlat2.mm"
include "simprl.mm"
include "sylbi.mm"
include "wceq.mm"
include "neeq1.mm"
include "neeq2.mm"
include "oveq1.mm"
include "breq2d.mm"
include "3anbi13d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "breq1.mm"
include "notbid.mm"
include "anbi12d.mm"
include "oveq2.mm"
include "ralbidv.mm"
include "3anbi23d.mm"
include "anbi2d.mm"
include "rspc2v.mm"
include "mpan9.mm"
include "3impb.mm"

theorem hlsuprexch
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let vx: setvar x
  let vy: setvar y
  assume hlsuprexch.b: |- B = ( Base ` K )
  assume hlsuprexch.l: |- .<_ = ( le ` K )
  assume hlsuprexch.j: |- .\/ = ( join ` K )
  assume hlsuprexch.a: |- A = ( Atoms ` K )

  disjoint A z
  disjoint B z
  disjoint K z
  disjoint P z
  disjoint Q z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint .\/ x
  disjoint .\/ y
  disjoint K x
  disjoint K y
  disjoint .<_ x
  disjoint .<_ y
  disjoint P x
  disjoint P y
  disjoint Q y
  assert |- ( ( K e. HL /\ P e. A /\ Q e. A ) -> ( ( P =/= Q -> E. z e. A ( z =/= P /\ z =/= Q /\ z .<_ ( P .\/ Q ) ) ) /\ A. z e. B ( ( -. P .<_ z /\ P .<_ ( z .\/ Q ) ) -> Q .<_ ( z .\/ P ) ) ) )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    cP
    cQ
    wne
    #
    vz
    cv
    #
    cP
    wne
    #
    @4
    cQ
    wne
    #
    @4
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    w3a
    #
    vz
    cA
    wrex
    #
    wi
    #
    cP
    @4
    c.le
    wbr
    #
    wn
    #
    cP
    @4
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    wa
    #
    cQ
    @4
    cP
    c.or
    co
    #
    c.le
    wbr
    #
    wi
    #
    vz
    cB
    wral
    #
    wa
    #
    @0
    vx
    cv
    #
    vy
    cv
    #
    wne
    #
    @4
    @22
    wne
    #
    @4
    @23
    wne
    #
    @4
    @22
    @23
    c.or
    co
    #
    c.le
    wbr
    #
    w3a
    #
    vz
    cA
    wrex
    #
    wi
    #
    @22
    @4
    c.le
    wbr
    #
    wn
    #
    @22
    @4
    @23
    c.or
    co
    #
    c.le
    wbr
    #
    wa
    #
    @23
    @4
    @22
    c.or
    co
    #
    c.le
    wbr
    #
    wi
    #
    vz
    cB
    wral
    #
    wa
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    @1
    @2
    wa
    @21
    @0
    cK
    coml
    wcel
    cK
    ccla
    wcel
    cK
    cal
    wcel
    w3a
    #
    @42
    cK
    cp0
    cfv
    #
    @22
    cK
    cplt
    cfv
    #
    wbr
    @22
    @23
    @45
    wbr
    wa
    @23
    @4
    @45
    wbr
    @4
    cK
    cp1
    cfv
    #
    @45
    wbr
    wa
    wa
    vz
    cB
    wrex
    vy
    cB
    wrex
    vx
    cB
    wrex
    #
    wa
    wa
    @42
    vx
    vy
    vz
    cA
    cB
    @45
    @46
    c.or
    cK
    c.le
    @44
    hlsuprexch.b
    hlsuprexch.l
    @45
    eqid
    hlsuprexch.j
    @44
    eqid
    @46
    eqid
    hlsuprexch.a
    ishlat2
    @43
    @42
    @47
    simprl
    sylbi
    @41
    @21
    cP
    @23
    wne
    #
    @5
    @26
    @4
    cP
    @23
    c.or
    co
    #
    c.le
    wbr
    #
    w3a
    #
    vz
    cA
    wrex
    #
    wi
    #
    @13
    cP
    @34
    c.le
    wbr
    #
    wa
    #
    @23
    @17
    c.le
    wbr
    #
    wi
    #
    vz
    cB
    wral
    #
    wa
    vx
    vy
    cP
    cQ
    cA
    cA
    @22
    cP
    wceq
    #
    @31
    @53
    @40
    @58
    @59
    @24
    @48
    @30
    @52
    @22
    cP
    @23
    neeq1
    @59
    @29
    @51
    vz
    cA
    @59
    @25
    @5
    @28
    @50
    @26
    @22
    cP
    @4
    neeq2
    @59
    @27
    @49
    @4
    c.le
    @22
    cP
    @23
    c.or
    oveq1
    breq2d
    3anbi13d
    rexbidv
    imbi12d
    @59
    @39
    @57
    vz
    cB
    @59
    @36
    @55
    @38
    @56
    @59
    @33
    @13
    @35
    @54
    @59
    @32
    @12
    @22
    cP
    @4
    c.le
    breq1
    notbid
    @22
    cP
    @34
    c.le
    breq1
    anbi12d
    @59
    @37
    @17
    @23
    c.le
    @22
    cP
    @4
    c.or
    oveq2
    breq2d
    imbi12d
    ralbidv
    anbi12d
    @23
    cQ
    wceq
    #
    @53
    @11
    @58
    @20
    @60
    @48
    @3
    @52
    @10
    @23
    cQ
    cP
    neeq2
    @60
    @51
    @9
    vz
    cA
    @60
    @26
    @6
    @50
    @8
    @5
    @23
    cQ
    @4
    neeq2
    @60
    @49
    @7
    @4
    c.le
    @23
    cQ
    cP
    c.or
    oveq2
    breq2d
    3anbi23d
    rexbidv
    imbi12d
    @60
    @57
    @19
    vz
    cB
    @60
    @55
    @16
    @56
    @18
    @60
    @54
    @15
    @13
    @60
    @34
    @14
    cP
    c.le
    @23
    cQ
    @4
    c.or
    oveq2
    breq2d
    anbi2d
    @23
    cQ
    @17
    c.le
    breq1
    imbi12d
    ralbidv
    anbi12d
    rspc2v
    mpan9
    3impb
end
