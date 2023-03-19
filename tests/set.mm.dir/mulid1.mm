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
include "c1.mm"
include "cnre.mm"
include "wa.mm"
include "recn.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "ax-1cn.mm"
include "adddir.mm"
include "mp3an3.mm"
include "syl2an.mm"
include "ax-1rid.mm"
include "mulass.mm"
include "mp3an13.mm"
include "syl.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "oveqan12d.mm"
include "oveq1.mm"
include "id.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "rexlimivv.mm"

theorem mulid1
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. CC -> ( A x. 1 ) = A )

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
    cA
    c1
    cmul
    co
    #
    cA
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
    @3
    c1
    cmul
    co
    #
    @3
    wceq
    @9
    @10
    @0
    c1
    cmul
    co
    #
    @2
    c1
    cmul
    co
    #
    caddc
    co
    #
    @3
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
    @13
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
    @15
    ax-icn
    @1
    recn
    #
    ci
    @1
    mulcl
    sylancr
    @14
    @15
    c1
    cc
    wcel
    #
    @16
    ax-1cn
    @0
    @2
    c1
    adddir
    mp3an3
    syl2an
    @7
    @8
    @11
    @0
    @12
    @2
    caddc
    @0
    ax-1rid
    @8
    @12
    ci
    @1
    c1
    cmul
    co
    #
    cmul
    co
    #
    @2
    @8
    @18
    @12
    @22
    wceq
    #
    @19
    @17
    @18
    @20
    @23
    ax-icn
    ax-1cn
    ci
    @1
    c1
    mulass
    mp3an13
    syl
    @8
    @21
    @1
    ci
    cmul
    @1
    ax-1rid
    oveq2d
    eqtrd
    oveqan12d
    eqtrd
    @4
    @5
    @10
    cA
    @3
    cA
    @3
    c1
    cmul
    oveq1
    @4
    id
    eqeq12d
    syl5ibrcom
    rexlimivv
    syl
end
