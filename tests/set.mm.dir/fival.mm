include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "cint.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "cab.mm"
include "cfi.mm"
include "cfv.mm"
include "elex.mm"
include "cuni.mm"
include "wss.mm"
include "wa.mm"
include "simpr.mm"
include "c0.mm"
include "wne.mm"
include "inss1.mm"
include "sseli.mm"
include "elpwid.mm"
include "eqvisset.mm"
include "intex.mm"
include "sylibr.mm"
include "intssuni2.mm"
include "syl2an.mm"
include "eqsstrd.mm"
include "selpw.mm"
include "rexlimiva.mm"
include "abssi.mm"
include "uniexg.mm"
include "pwexg.mm"
include "syl.mm"
include "ssexg.mm"
include "sylancr.mm"
include "pweq.mm"
include "ineq1d.mm"
include "rexeqdv.mm"
include "abbidv.mm"
include "df-fi.mm"
include "fvmptg.mm"
include "syl2anc.mm"

theorem fival
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cV: class V
  let vz: setvar z
  let cB: class B
  let cW: class W

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint V x
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint W x
  assert |- ( A e. V -> ( fi ` A ) = { y | E. x e. ( ~P A i^i Fin ) y = |^| x } )

  proof
    cA
    cV
    wcel
    #
    cA
    cvv
    wcel
    vy
    cv
    #
    vx
    cv
    #
    cint
    #
    wceq
    #
    vx
    cA
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    vy
    cab
    #
    cvv
    wcel
    #
    cA
    cfi
    cfv
    @8
    wceq
    cA
    cV
    elex
    @0
    @8
    cA
    cuni
    #
    cpw
    #
    wss
    @11
    cvv
    wcel
    #
    @9
    @7
    vy
    @11
    @4
    @1
    @11
    wcel
    #
    vx
    @6
    @2
    @6
    wcel
    #
    @4
    wa
    #
    @1
    @10
    wss
    @13
    @15
    @1
    @3
    @10
    @14
    @4
    simpr
    @14
    @2
    cA
    wss
    @2
    c0
    wne
    #
    @3
    @10
    wss
    @4
    @14
    @2
    cA
    @6
    @5
    @2
    @5
    cfn
    inss1
    sseli
    elpwid
    @4
    @3
    cvv
    wcel
    @16
    vy
    @3
    eqvisset
    @2
    intex
    sylibr
    @2
    cA
    intssuni2
    syl2an
    eqsstrd
    vy
    @10
    selpw
    sylibr
    rexlimiva
    abssi
    @0
    @10
    cvv
    wcel
    @12
    cA
    cV
    uniexg
    @10
    cvv
    pwexg
    syl
    @8
    @11
    cvv
    ssexg
    sylancr
    vz
    cA
    @4
    vx
    vz
    cv
    #
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    vy
    cab
    @8
    cvv
    cvv
    cfi
    @17
    cA
    wceq
    #
    @20
    @7
    vy
    @21
    @4
    vx
    @19
    @6
    @21
    @18
    @5
    cfn
    @17
    cA
    pweq
    ineq1d
    rexeqdv
    abbidv
    vz
    vx
    vy
    df-fi
    fvmptg
    syl2anc
end
