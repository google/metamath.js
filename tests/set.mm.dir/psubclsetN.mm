include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "wss.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cab.mm"
include "elex.mm"
include "cpscN.mm"
include "catm.mm"
include "cpolN.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "sseq2d.mm"
include "fveq1d.mm"
include "fveq12d.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "abbidv.mm"
include "df-psubclN.mm"
include "cpw.mm"
include "fvex.mm"
include "eqeltri.mm"
include "pwex.mm"
include "selpw.mm"
include "anbi1i.mm"
include "abbii.mm"
include "ssab2.mm"
include "eqsstr3i.mm"
include "ssexi.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "syl.mm"

theorem psubclsetN
  let cA: class A
  let cB: class B
  let cC: class C
  let cK: class K
  let c.pe: class ._|_
  let vs: setvar s
  let vk: setvar k
  assume psubclset.a: |- A = ( Atoms ` K )
  assume psubclset.p: |- ._|_ = ( _|_P ` K )
  assume psubclset.c: |- C = ( PSubCl ` K )

  disjoint A s
  disjoint K s
  disjoint k s
  disjoint A k
  disjoint K k
  disjoint ._|_ k
  assert |- ( K e. B -> C = { s | ( s C_ A /\ ( ._|_ ` ( ._|_ ` s ) ) = s ) } )

  proof
    cK
    cB
    wcel
    cK
    cvv
    wcel
    #
    cC
    vs
    cv
    #
    cA
    wss
    #
    @1
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @1
    wceq
    #
    wa
    #
    vs
    cab
    #
    wceq
    cK
    cB
    elex
    @0
    cC
    cK
    cpscN
    cfv
    @7
    psubclset.c
    vk
    cK
    @1
    vk
    cv
    #
    catm
    cfv
    #
    wss
    #
    @1
    @8
    cpolN
    cfv
    #
    cfv
    #
    @11
    cfv
    #
    @1
    wceq
    #
    wa
    #
    vs
    cab
    @7
    cvv
    cpscN
    @8
    cK
    wceq
    #
    @15
    @6
    vs
    @16
    @10
    @2
    @14
    @5
    @16
    @9
    cA
    @1
    @16
    @9
    cK
    catm
    cfv
    #
    cA
    @8
    cK
    catm
    fveq2
    psubclset.a
    syl6eqr
    sseq2d
    @16
    @13
    @4
    @1
    @16
    @12
    @3
    @11
    c.pe
    @16
    @11
    cK
    cpolN
    cfv
    c.pe
    @8
    cK
    cpolN
    fveq2
    psubclset.p
    syl6eqr
    #
    @16
    @1
    @11
    c.pe
    @18
    fveq1d
    fveq12d
    eqeq1d
    anbi12d
    abbidv
    vk
    vs
    df-psubclN
    @7
    cA
    cpw
    #
    cA
    cA
    @17
    cvv
    psubclset.a
    cK
    catm
    fvex
    eqeltri
    pwex
    @7
    @1
    @19
    wcel
    #
    @5
    wa
    #
    vs
    cab
    @19
    @21
    @6
    vs
    @20
    @2
    @5
    vs
    cA
    selpw
    anbi1i
    abbii
    @5
    vs
    @19
    ssab2
    eqsstr3i
    ssexi
    fvmpt
    syl5eq
    syl
end
