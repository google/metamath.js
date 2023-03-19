include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cr.mm"
include "wrex.mm"
include "cc0.mm"
include "cnre.mm"
include "wa.mm"
include "recn.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "0cn.mm"
include "adddi.mm"
include "mp3an1.mm"
include "syl2an.mm"
include "mul02lem2.mm"
include "mul12.mm"
include "mp3an12.mm"
include "syl.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "oveqan12d.mm"
include "ax-mp.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "rexlimivv.mm"
include "0re.mm"
include "eqtr3i.mm"
include "syl6eq.mm"

theorem mul02
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. CC -> ( 0 x. A ) = 0 )

  proof
    cA
    cc
    wcel
    cA
    vx
    cv
    #
    ci
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
    cr
    wrex
    vx
    cr
    wrex
    cc0
    cA
    cmul
    co
    #
    cc0
    wceq
    #
    vx
    vy
    cA
    cnre
    @4
    @6
    vx
    vy
    cr
    cr
    @0
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    wa
    #
    @6
    @4
    cc0
    @3
    cmul
    co
    #
    cc0
    wceq
    @9
    @10
    cc0
    ci
    cc0
    cmul
    co
    #
    caddc
    co
    #
    cc0
    @9
    @10
    cc0
    @0
    cmul
    co
    #
    cc0
    @2
    cmul
    co
    #
    caddc
    co
    #
    @12
    @7
    @0
    cc
    wcel
    #
    @2
    cc
    wcel
    #
    @10
    @15
    wceq
    #
    @8
    @0
    recn
    @8
    ci
    cc
    wcel
    #
    @1
    cc
    wcel
    #
    @17
    ax-icn
    @1
    recn
    #
    ci
    @1
    mulcl
    sylancr
    cc0
    cc
    wcel
    #
    @16
    @17
    @18
    0cn
    cc0
    @0
    @2
    adddi
    mp3an1
    syl2an
    @7
    @8
    @13
    cc0
    @14
    @11
    caddc
    @0
    mul02lem2
    @8
    @14
    ci
    cc0
    @1
    cmul
    co
    #
    cmul
    co
    #
    @11
    @8
    @20
    @14
    @24
    wceq
    #
    @21
    @22
    @19
    @20
    @25
    0cn
    ax-icn
    cc0
    ci
    @1
    mul12
    mp3an12
    syl
    @8
    @23
    cc0
    ci
    cmul
    @1
    mul02lem2
    oveq2d
    eqtrd
    oveqan12d
    eqtrd
    #
    cc0
    cc0
    cmul
    co
    #
    @12
    cc0
    cc0
    @3
    wceq
    #
    vy
    cr
    wrex
    vx
    cr
    wrex
    #
    @27
    @12
    wceq
    #
    @22
    @29
    0cn
    vx
    vy
    cc0
    cnre
    ax-mp
    @28
    @30
    vx
    vy
    cr
    cr
    @9
    @30
    @28
    @10
    @12
    wceq
    @26
    @28
    @27
    @10
    @12
    cc0
    @3
    cc0
    cmul
    oveq2
    eqeq1d
    syl5ibrcom
    rexlimivv
    ax-mp
    cc0
    cr
    wcel
    @27
    cc0
    wceq
    0re
    cc0
    mul02lem2
    ax-mp
    eqtr3i
    syl6eq
    @4
    @5
    @10
    cc0
    cA
    @3
    cc0
    cmul
    oveq2
    eqeq1d
    syl5ibrcom
    rexlimivv
    syl
end
