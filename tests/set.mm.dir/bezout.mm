include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "wceq.mm"
include "cgcd.mm"
include "co.mm"
include "cv.mm"
include "cmul.mm"
include "caddc.mm"
include "wrex.mm"
include "wn.mm"
include "cn.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "oveq2d.mm"
include "cbvrex2v.mm"
include "syl6bb.mm"
include "cbvrabv.mm"
include "simpll.mm"
include "simplr.mm"
include "eqid.mm"
include "simpr.mm"
include "bezoutlem4.mm"
include "elrab.mm"
include "simprbi.mm"
include "syl.mm"
include "ex.mm"
include "0z.mm"
include "00id.mm"
include "0cn.mm"
include "mul01i.mm"
include "oveq12i.mm"
include "gcd0val.mm"
include "3eqtr4ri.mm"
include "rspc2ev.mm"
include "mp3an.mm"
include "oveq12.mm"
include "oveq1.mm"
include "oveqan12d.mm"
include "eqeq12d.mm"
include "mpbiri.mm"
include "pm2.61d2.mm"

theorem bezout
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B s
  disjoint B t
  disjoint B u
  disjoint B v
  disjoint B z
  assert |- ( ( A e. ZZ /\ B e. ZZ ) -> E. x e. ZZ E. y e. ZZ ( A gcd B ) = ( ( A x. x ) + ( B x. y ) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    #
    cA
    cc0
    wceq
    #
    cB
    cc0
    wceq
    #
    wa
    #
    cA
    cB
    cgcd
    co
    #
    cA
    vx
    cv
    #
    cmul
    co
    #
    cB
    vy
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vy
    cz
    wrex
    vx
    cz
    wrex
    #
    @2
    @5
    wn
    #
    @13
    @2
    @14
    wa
    #
    @6
    vz
    cv
    #
    @11
    wceq
    #
    vy
    cz
    wrex
    vx
    cz
    wrex
    #
    vz
    cn
    crab
    #
    wcel
    #
    @13
    @15
    vu
    vv
    vt
    cA
    cB
    @19
    cr
    clt
    cinf
    #
    @19
    @18
    vt
    cv
    #
    cA
    vu
    cv
    #
    cmul
    co
    #
    cB
    vv
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vv
    cz
    wrex
    vu
    cz
    wrex
    #
    vz
    vt
    cn
    @16
    @22
    wceq
    #
    @18
    @22
    @11
    wceq
    #
    vy
    cz
    wrex
    vx
    cz
    wrex
    @29
    @30
    @17
    @31
    vx
    vy
    cz
    cz
    @16
    @22
    @11
    eqeq1
    2rexbidv
    @31
    @28
    @22
    @24
    @10
    caddc
    co
    #
    wceq
    vx
    vy
    vu
    vv
    cz
    cz
    @7
    @23
    wceq
    #
    @11
    @32
    @22
    @33
    @8
    @24
    @10
    caddc
    @7
    @23
    cA
    cmul
    oveq2
    oveq1d
    eqeq2d
    @9
    @25
    wceq
    #
    @32
    @27
    @22
    @34
    @10
    @26
    @24
    caddc
    @9
    @25
    cB
    cmul
    oveq2
    oveq2d
    eqeq2d
    cbvrex2v
    syl6bb
    cbvrabv
    @0
    @1
    @14
    simpll
    @0
    @1
    @14
    simplr
    @21
    eqid
    @2
    @14
    simpr
    bezoutlem4
    @20
    @6
    cn
    wcel
    @13
    @18
    @13
    vz
    @6
    cn
    @16
    @6
    wceq
    @17
    @12
    vx
    vy
    cz
    cz
    @16
    @6
    @11
    eqeq1
    2rexbidv
    elrab
    simprbi
    syl
    ex
    @5
    @13
    cc0
    cc0
    cgcd
    co
    #
    cc0
    @7
    cmul
    co
    #
    cc0
    @9
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vy
    cz
    wrex
    vx
    cz
    wrex
    #
    cc0
    cz
    wcel
    #
    @41
    @35
    cc0
    cc0
    cmul
    co
    #
    @42
    caddc
    co
    #
    wceq
    #
    @40
    0z
    0z
    cc0
    cc0
    caddc
    co
    cc0
    @43
    @35
    00id
    @42
    cc0
    @42
    cc0
    caddc
    cc0
    0cn
    mul01i
    #
    @45
    oveq12i
    gcd0val
    3eqtr4ri
    @39
    @44
    @35
    @42
    @37
    caddc
    co
    #
    wceq
    vx
    vy
    cc0
    cc0
    cz
    cz
    @7
    cc0
    wceq
    #
    @38
    @46
    @35
    @47
    @36
    @42
    @37
    caddc
    @7
    cc0
    cc0
    cmul
    oveq2
    oveq1d
    eqeq2d
    @9
    cc0
    wceq
    #
    @46
    @43
    @35
    @48
    @37
    @42
    @42
    caddc
    @9
    cc0
    cc0
    cmul
    oveq2
    oveq2d
    eqeq2d
    rspc2ev
    mp3an
    @5
    @12
    @39
    vx
    vy
    cz
    cz
    @5
    @6
    @35
    @11
    @38
    cA
    cc0
    cB
    cc0
    cgcd
    oveq12
    @3
    @4
    @8
    @36
    @10
    @37
    caddc
    cA
    cc0
    @7
    cmul
    oveq1
    cB
    cc0
    @9
    cmul
    oveq1
    oveqan12d
    eqeq12d
    2rexbidv
    mpbiri
    pm2.61d2
end
