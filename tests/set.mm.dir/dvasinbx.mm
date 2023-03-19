include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "csin.mm"
include "cfv.mm"
include "cmpt.mm"
include "cdv.mm"
include "cc0.mm"
include "ccos.mm"
include "caddc.mm"
include "cr.mm"
include "cpr.mm"
include "cnelprrecn.mm"
include "a1i.mm"
include "simpll.mm"
include "0cnd.mm"
include "wceq.mm"
include "id.mm"
include "dvmptc.mm"
include "adantr.mm"
include "mulcl.mm"
include "sincld.mm"
include "adantll.mm"
include "simpl.mm"
include "coscld.mm"
include "mulcld.mm"
include "dvsinax.mm"
include "adantl.mm"
include "dvmptmul.mm"
include "mul02d.mm"
include "mul32d.mm"
include "simpr.mm"
include "mulcomd.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "addid2d.mm"
include "mpteq2dva.mm"

theorem dvasinbx
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x

  disjoint A y
  disjoint B y
  disjoint k x
  assert |- ( ( A e. CC /\ B e. CC ) -> ( CC _D ( y e. CC |-> ( A x. ( sin ` ( B x. y ) ) ) ) ) = ( y e. CC |-> ( ( A x. B ) x. ( cos ` ( B x. y ) ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cc
    vy
    cc
    cA
    cB
    vy
    cv
    #
    cmul
    co
    #
    csin
    cfv
    #
    cmul
    co
    cmpt
    cdv
    co
    vy
    cc
    cc0
    @5
    cmul
    co
    #
    cB
    @4
    ccos
    cfv
    #
    cmul
    co
    #
    cA
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    vy
    cc
    cA
    cB
    cmul
    co
    #
    @7
    cmul
    co
    #
    cmpt
    @2
    vy
    cA
    cc0
    @5
    @8
    cc
    cc
    cc
    cc
    cc
    cr
    cc
    cpr
    wcel
    #
    @2
    cnelprrecn
    a1i
    @0
    @1
    @3
    cc
    wcel
    #
    simpll
    #
    @2
    @14
    wa
    #
    0cnd
    @0
    cc
    vy
    cc
    cA
    cmpt
    cdv
    co
    vy
    cc
    cc0
    cmpt
    wceq
    @1
    @0
    vy
    cA
    cc
    @13
    @0
    cnelprrecn
    a1i
    @0
    id
    dvmptc
    adantr
    @1
    @14
    @5
    cc
    wcel
    @0
    @1
    @14
    wa
    #
    @4
    cB
    @3
    mulcl
    #
    sincld
    adantll
    #
    @1
    @14
    @8
    cc
    wcel
    @0
    @17
    cB
    @7
    @1
    @14
    simpl
    #
    @17
    @4
    @18
    coscld
    #
    mulcld
    adantll
    @1
    cc
    vy
    cc
    @5
    cmpt
    cdv
    co
    vy
    cc
    @8
    cmpt
    wceq
    @0
    vy
    cB
    dvsinax
    adantl
    dvmptmul
    @2
    vy
    cc
    @10
    @12
    @16
    @10
    cc0
    @12
    caddc
    co
    @12
    @16
    @6
    cc0
    @9
    @12
    caddc
    @16
    @5
    @19
    mul02d
    @16
    @9
    cB
    cA
    cmul
    co
    #
    @7
    cmul
    co
    @12
    @16
    cB
    @7
    cA
    @1
    @14
    @1
    @0
    @20
    adantll
    #
    @1
    @14
    @7
    cc
    wcel
    @0
    @21
    adantll
    #
    @15
    mul32d
    @16
    @22
    @11
    @7
    cmul
    @2
    @22
    @11
    wceq
    @14
    @2
    cB
    cA
    @0
    @1
    simpr
    @0
    @1
    simpl
    mulcomd
    adantr
    oveq1d
    eqtrd
    oveq12d
    @16
    @12
    @16
    @11
    @7
    @16
    cA
    cB
    @15
    @23
    mulcld
    @24
    mulcld
    addid2d
    eqtrd
    mpteq2dva
    eqtrd
end
