include "com.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wn.mm"
include "w3a.mm"
include "csuc.mm"
include "cfv.mm"
include "wss.mm"
include "simpr1.mm"
include "ackbij1lem3.mm"
include "syl.mm"
include "wceq.mm"
include "simpr3.mm"
include "ackbij1lem1.mm"
include "inss2.mm"
include "syl6eqss.mm"
include "ackbij1lem12.mm"
include "syl2anc.mm"
include "csn.mm"
include "wpss.mm"
include "con0.mm"
include "ackbij1lem10.mm"
include "ffvelrni.mm"
include "nnon.mm"
include "onpsssuc.mm"
include "4syl.mm"
include "ackbij1lem14.mm"
include "psseq2d.mm"
include "mpbird.mm"
include "simpll.mm"
include "inss1.mm"
include "ackbij1lem11.mm"
include "sylancl.mm"
include "cun.mm"
include "ssun1.mm"
include "simpr2.mm"
include "ackbij1lem2.mm"
include "syl5sseqr.mm"
include "psssstrd.mm"
include "sspsstrd.mm"
include "pssned.mm"
include "necomd.mm"
include "neneqd.mm"

theorem ackbij1lem15
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let vc: setvar c
  let va: setvar a
  let vb: setvar b
  let cG: class G
  let cH: class H
  assume ackbij.f: |- F = ( x e. ( ~P _om i^i Fin ) |-> ( card ` U_ y e. x ( { y } X. ~P y ) ) )

  disjoint F c
  disjoint F x
  disjoint F y
  disjoint c x
  disjoint c y
  disjoint x y
  disjoint A c
  disjoint A x
  disjoint A y
  disjoint B c
  disjoint B x
  disjoint B y
  disjoint F a
  disjoint F b
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G x
  disjoint G y
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint H x
  disjoint H y
  disjoint A a
  disjoint A b
  disjoint B a
  disjoint B b
  assert |- ( ( ( A e. ( ~P _om i^i Fin ) /\ B e. ( ~P _om i^i Fin ) ) /\ ( c e. _om /\ c e. A /\ -. c e. B ) ) -> -. ( F ` ( A i^i suc c ) ) = ( F ` ( B i^i suc c ) ) )

  proof
    cA
    com
    cpw
    cfn
    cin
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    vc
    cv
    #
    com
    wcel
    #
    @4
    cA
    wcel
    #
    @4
    cB
    wcel
    wn
    #
    w3a
    #
    wa
    #
    cA
    @4
    csuc
    #
    cin
    #
    cF
    cfv
    #
    cB
    @10
    cin
    #
    cF
    cfv
    #
    @9
    @14
    @12
    @9
    @14
    @12
    @9
    @14
    @4
    cF
    cfv
    #
    @12
    @9
    @4
    @0
    wcel
    #
    @13
    @4
    wss
    @14
    @15
    wss
    @9
    @5
    @16
    @3
    @5
    @6
    @7
    simpr1
    #
    @4
    ackbij1lem3
    syl
    #
    @9
    @13
    cB
    @4
    cin
    #
    @4
    @9
    @7
    @13
    @19
    wceq
    @3
    @5
    @6
    @7
    simpr3
    @4
    cB
    ackbij1lem1
    syl
    cB
    @4
    inss2
    syl6eqss
    vx
    vy
    @13
    @4
    cF
    ackbij.f
    ackbij1lem12
    syl2anc
    @9
    @15
    @4
    csn
    #
    cF
    cfv
    #
    @12
    @9
    @15
    @21
    wpss
    @15
    @15
    csuc
    #
    wpss
    #
    @9
    @16
    @15
    com
    wcel
    @15
    con0
    wcel
    @23
    @18
    @0
    com
    @4
    cF
    vx
    vy
    cF
    ackbij.f
    ackbij1lem10
    ffvelrni
    @15
    nnon
    @15
    onpsssuc
    4syl
    @9
    @21
    @22
    @15
    @9
    @5
    @21
    @22
    wceq
    @17
    vx
    vy
    @4
    cF
    ackbij.f
    ackbij1lem14
    syl
    psseq2d
    mpbird
    @9
    @11
    @0
    wcel
    #
    @20
    @11
    wss
    @21
    @12
    wss
    @9
    @1
    @11
    cA
    wss
    @24
    @1
    @2
    @8
    simpll
    cA
    @10
    inss1
    vx
    vy
    cA
    @11
    cF
    ackbij.f
    ackbij1lem11
    sylancl
    @9
    @20
    cA
    @4
    cin
    #
    cun
    #
    @20
    @11
    @20
    @25
    ssun1
    @9
    @6
    @11
    @26
    wceq
    @3
    @5
    @6
    @7
    simpr2
    @4
    cA
    ackbij1lem2
    syl
    syl5sseqr
    vx
    vy
    @20
    @11
    cF
    ackbij.f
    ackbij1lem12
    syl2anc
    psssstrd
    sspsstrd
    pssned
    necomd
    neneqd
end
