include "chil.mm"
include "wss.mm"
include "cpw.mm"
include "wcel.mm"
include "cv.mm"
include "csh.mm"
include "crab.mm"
include "cint.mm"
include "cvv.mm"
include "cspn.mm"
include "cfv.mm"
include "wceq.mm"
include "ax-hilex.mm"
include "elpw2.mm"
include "biimpri.mm"
include "wrex.mm"
include "helsh.mm"
include "sseq2.mm"
include "rspcev.mm"
include "mpan.mm"
include "intexrab.mm"
include "sylib.mm"
include "sseq1.mm"
include "rabbidv.mm"
include "inteqd.mm"
include "df-span.mm"
include "fvmptg.mm"
include "syl2anc.mm"

theorem spanval
  let vx: setvar x
  let cA: class A
  let vf: setvar f
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cD: class D

  disjoint A x
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint D x
  disjoint D y
  assert |- ( A C_ ~H -> ( span ` A ) = |^| { x e. SH | A C_ x } )

  proof
    cA
    chil
    wss
    #
    cA
    chil
    cpw
    #
    wcel
    #
    cA
    vx
    cv
    #
    wss
    #
    vx
    csh
    crab
    #
    cint
    #
    cvv
    wcel
    #
    cA
    cspn
    cfv
    @6
    wceq
    @2
    @0
    cA
    chil
    ax-hilex
    elpw2
    biimpri
    @0
    @4
    vx
    csh
    wrex
    #
    @7
    chil
    csh
    wcel
    @0
    @8
    helsh
    @4
    @0
    vx
    chil
    csh
    @3
    chil
    cA
    sseq2
    rspcev
    mpan
    @4
    vx
    csh
    intexrab
    sylib
    vy
    cA
    vy
    cv
    #
    @3
    wss
    #
    vx
    csh
    crab
    #
    cint
    @6
    @1
    cvv
    cspn
    @9
    cA
    wceq
    #
    @11
    @5
    @12
    @10
    @4
    vx
    csh
    @9
    cA
    @3
    sseq1
    rabbidv
    inteqd
    vy
    vx
    df-span
    fvmptg
    syl2anc
end
