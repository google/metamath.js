include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cort.mm"
include "cin.mm"
include "chj.mm"
include "co.mm"
include "wa.mm"
include "caddc.mm"
include "cst.mm"
include "wcel.mm"
include "cv.mm"
include "wi.mm"
include "wss.mm"
include "cch.mm"
include "wral.mm"
include "simplbi.mm"
include "stji1i.mm"
include "syl.mm"
include "adantr.mm"
include "chil.mm"
include "stcltr2i.mm"
include "imp.mm"
include "ineq2.mm"
include "chm1i.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "cr.mm"
include "choccli.mm"
include "stcl.mm"
include "mpi.mm"
include "recnd.mm"
include "addcomd.mm"
include "sto1i.mm"
include "eqtrd.mm"
include "ex.mm"

theorem stcltrlem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cS: class S
  assume stcltr1.1: |- ( ph <-> ( S e. States /\ A. x e. CH A. y e. CH ( ( ( S ` x ) = 1 -> ( S ` y ) = 1 ) -> x C_ y ) ) )
  assume stcltr1.2: |- A e. CH
  assume stcltrlem1.3: |- B e. CH

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint S x
  disjoint S y
  assert |- ( ph -> ( ( S ` B ) = 1 -> ( S ` ( ( _|_ ` A ) vH ( A i^i B ) ) ) = 1 ) )

  proof
    wph
    cB
    cS
    cfv
    c1
    wceq
    #
    cA
    cort
    cfv
    #
    cA
    cB
    cin
    #
    chj
    co
    cS
    cfv
    #
    c1
    wceq
    wph
    @0
    wa
    #
    @3
    @1
    cS
    cfv
    #
    @2
    cS
    cfv
    #
    caddc
    co
    #
    c1
    wph
    @3
    @7
    wceq
    #
    @0
    wph
    cS
    cst
    wcel
    #
    @8
    wph
    @9
    vx
    cv
    #
    cS
    cfv
    c1
    wceq
    vy
    cv
    #
    cS
    cfv
    c1
    wceq
    wi
    @10
    @11
    wss
    wi
    vy
    cch
    wral
    vx
    cch
    wral
    stcltr1.1
    simplbi
    #
    cA
    cB
    cS
    stcltr1.2
    stcltrlem1.3
    stji1i
    syl
    adantr
    @4
    @7
    @5
    cA
    cS
    cfv
    #
    caddc
    co
    #
    c1
    @4
    @6
    @13
    @5
    caddc
    @4
    @2
    cA
    cS
    @4
    cB
    chil
    wceq
    #
    @2
    cA
    wceq
    wph
    @0
    @15
    wph
    vx
    vy
    cB
    cS
    stcltr1.1
    stcltrlem1.3
    stcltr2i
    imp
    @15
    @2
    cA
    chil
    cin
    cA
    cB
    chil
    cA
    ineq2
    cA
    stcltr1.2
    chm1i
    syl6eq
    syl
    fveq2d
    oveq2d
    @4
    @9
    @14
    c1
    wceq
    wph
    @9
    @0
    @12
    adantr
    @9
    @14
    @13
    @5
    caddc
    co
    c1
    @9
    @5
    @13
    @9
    @5
    @9
    @1
    cch
    wcel
    @5
    cr
    wcel
    cA
    stcltr1.2
    choccli
    @1
    cS
    stcl
    mpi
    recnd
    @9
    @13
    @9
    cA
    cch
    wcel
    @13
    cr
    wcel
    stcltr1.2
    cA
    cS
    stcl
    mpi
    recnd
    addcomd
    cA
    cS
    stcltr1.2
    sto1i
    eqtrd
    syl
    eqtrd
    eqtrd
    ex
end
