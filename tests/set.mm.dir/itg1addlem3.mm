include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "wceq.mm"
include "wn.mm"
include "co.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "cvol.mm"
include "cfv.mm"
include "cif.mm"
include "cv.mm"
include "eqeq1.mm"
include "bi2anan9.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "ineqan12d.mm"
include "fveq2d.mm"
include "ifbieq2d.mm"
include "c0ex.mm"
include "fvex.mm"
include "ifex.mm"
include "ovmpt2a.mm"
include "iffalse.mm"
include "sylan9eq.mm"

theorem itg1addlem3
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vi: setvar i
  let vj: setvar j
  let cF: class F
  let cG: class G
  let cI: class I
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vx: setvar x
  let cP: class P
  let vu: setvar u
  assume i1fadd.1: |- ( ph -> F e. dom S.1 )
  assume i1fadd.2: |- ( ph -> G e. dom S.1 )
  assume itg1add.3: |- I = ( i e. RR , j e. RR |-> if ( ( i = 0 /\ j = 0 ) , 0 , ( vol ` ( ( `' F " { i } ) i^i ( `' G " { j } ) ) ) ) )

  disjoint i j
  disjoint A i
  disjoint A j
  disjoint B i
  disjoint B j
  disjoint F i
  disjoint F j
  disjoint G i
  disjoint G j
  disjoint i ph
  disjoint j ph
  disjoint i y
  disjoint i z
  disjoint j y
  disjoint j z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint w y
  disjoint I w
  disjoint I y
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint P v
  disjoint w x
  disjoint w z
  disjoint P w
  disjoint x y
  disjoint x z
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint i x
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  assert |- ( ( ( A e. RR /\ B e. RR ) /\ -. ( A = 0 /\ B = 0 ) ) -> ( A I B ) = ( vol ` ( ( `' F " { A } ) i^i ( `' G " { B } ) ) ) )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    wa
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
    wn
    cA
    cB
    cI
    co
    @2
    cc0
    cF
    ccnv
    #
    cA
    csn
    #
    cima
    #
    cG
    ccnv
    #
    cB
    csn
    #
    cima
    #
    cin
    #
    cvol
    cfv
    #
    cif
    #
    @10
    vi
    vj
    cA
    cB
    cr
    cr
    vi
    cv
    #
    cc0
    wceq
    #
    vj
    cv
    #
    cc0
    wceq
    #
    wa
    #
    cc0
    @3
    @12
    csn
    #
    cima
    #
    @6
    @14
    csn
    #
    cima
    #
    cin
    #
    cvol
    cfv
    #
    cif
    @11
    cI
    @12
    cA
    wceq
    #
    @14
    cB
    wceq
    #
    wa
    #
    @16
    @2
    @22
    @10
    cc0
    @23
    @13
    @0
    @24
    @15
    @1
    @12
    cA
    cc0
    eqeq1
    @14
    cB
    cc0
    eqeq1
    bi2anan9
    @25
    @21
    @9
    cvol
    @23
    @24
    @18
    @5
    @20
    @8
    @23
    @17
    @4
    @3
    @12
    cA
    sneq
    imaeq2d
    @24
    @19
    @7
    @6
    @14
    cB
    sneq
    imaeq2d
    ineqan12d
    fveq2d
    ifbieq2d
    itg1add.3
    @2
    cc0
    @10
    c0ex
    @9
    cvol
    fvex
    ifex
    ovmpt2a
    @2
    cc0
    @10
    iffalse
    sylan9eq
end
