include "wcel.mm"
include "cv.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cgz.mm"
include "wrex.mm"
include "cmul.mm"
include "2sqlem1.mm"
include "wa.mm"
include "reeanv.mm"
include "gzmulcl.mm"
include "cc.mm"
include "gzcn.mm"
include "absmul.mm"
include "syl2an.mm"
include "oveq1d.mm"
include "abscld.mm"
include "recnd.mm"
include "sqmul.mm"
include "eqtr2d.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "sylibr.mm"
include "oveq12.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "rexlimivv.mm"
include "sylbir.mm"
include "syl2anb.mm"

theorem mul2sq
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cS: class S
  let va: setvar a
  let vb: setvar b
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vm: setvar m
  let cC: class C
  let vu: setvar u
  let vv: setvar v
  let wph: wff ph
  let cM: class M
  let cD: class D
  let cE: class E
  let cN: class N
  let cY: class Y
  let cF: class F
  let cP: class P
  assume 2sq.1: |- S = ran ( w e. Z[i] |-> ( ( abs ` w ) ^ 2 ) )


  assert |- ( ( A e. S /\ B e. S ) -> ( A x. B ) e. S )

  proof
    cA
    cS
    wcel
    cA
    vx
    cv
    #
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    wceq
    #
    vx
    cgz
    wrex
    #
    cB
    vy
    cv
    #
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    wceq
    #
    vy
    cgz
    wrex
    #
    cA
    cB
    cmul
    co
    #
    cS
    wcel
    #
    cB
    cS
    wcel
    vx
    vw
    cA
    cS
    2sq.1
    2sqlem1
    vy
    vw
    cB
    cS
    2sq.1
    2sqlem1
    @4
    @9
    wa
    @3
    @8
    wa
    #
    vy
    cgz
    wrex
    vx
    cgz
    wrex
    @11
    @3
    @8
    vx
    vy
    cgz
    cgz
    reeanv
    @12
    @11
    vx
    vy
    cgz
    cgz
    @0
    cgz
    wcel
    #
    @5
    cgz
    wcel
    #
    wa
    #
    @11
    @12
    @2
    @7
    cmul
    co
    #
    cS
    wcel
    #
    @15
    @16
    vz
    cv
    #
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    wceq
    #
    vz
    cgz
    wrex
    #
    @17
    @15
    @0
    @5
    cmul
    co
    #
    cgz
    wcel
    @16
    @23
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    wceq
    #
    @22
    @0
    @5
    gzmulcl
    @15
    @25
    @1
    @6
    cmul
    co
    #
    c2
    cexp
    co
    #
    @16
    @15
    @24
    @27
    c2
    cexp
    @13
    @0
    cc
    wcel
    @5
    cc
    wcel
    @24
    @27
    wceq
    @14
    @0
    gzcn
    #
    @5
    gzcn
    #
    @0
    @5
    absmul
    syl2an
    oveq1d
    @13
    @1
    cc
    wcel
    @6
    cc
    wcel
    @28
    @16
    wceq
    @14
    @13
    @1
    @13
    @0
    @29
    abscld
    recnd
    @14
    @6
    @14
    @5
    @30
    abscld
    recnd
    @1
    @6
    sqmul
    syl2an
    eqtr2d
    @21
    @26
    vz
    @23
    cgz
    @18
    @23
    wceq
    #
    @20
    @25
    @16
    @31
    @19
    @24
    c2
    cexp
    @18
    @23
    cabs
    fveq2
    oveq1d
    eqeq2d
    rspcev
    syl2anc
    vz
    vw
    @16
    cS
    2sq.1
    2sqlem1
    sylibr
    @12
    @10
    @16
    cS
    cA
    @2
    cB
    @7
    cmul
    oveq12
    eleq1d
    syl5ibrcom
    rexlimivv
    sylbir
    syl2anb
end
