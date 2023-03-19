include "wf.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "c2.mm"
include "cv.mm"
include "chash.mm"
include "cle.mm"
include "wbr.mm"
include "cpw.mm"
include "crab.mm"
include "eqid.mm"
include "feq23i.mm"
include "biimpi.mm"
include "ffvelrnda.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq2d.mm"
include "cbvrabv.mm"
include "elrab2.mm"
include "simprbi.mm"
include "syl.mm"

theorem lfgredgge2
  let vx: setvar x
  let cA: class A
  let cE: class E
  let cG: class G
  let cI: class I
  let cV: class V
  let cX: class X
  let vy: setvar y
  assume lfuhgrnloopv.i: |- I = ( iEdg ` G )
  assume lfuhgrnloopv.a: |- A = dom I
  assume lfuhgrnloopv.e: |- E = { x e. ~P V | 2 <_ ( # ` x ) }

  disjoint A x
  disjoint I x
  disjoint V x
  disjoint I y
  disjoint x y
  disjoint V y
  disjoint X y
  assert |- ( ( I : A --> E /\ X e. A ) -> 2 <_ ( # ` ( I ` X ) ) )

  proof
    cA
    cE
    cI
    wf
    #
    cX
    cA
    wcel
    wa
    cX
    cI
    cfv
    #
    c2
    vx
    cv
    #
    chash
    cfv
    #
    cle
    wbr
    #
    vx
    cV
    cpw
    #
    crab
    #
    wcel
    #
    c2
    @1
    chash
    cfv
    #
    cle
    wbr
    #
    @0
    cA
    @6
    cX
    cI
    @0
    cA
    @6
    cI
    wf
    cA
    cE
    cA
    @6
    cI
    cA
    eqid
    lfuhgrnloopv.e
    feq23i
    biimpi
    ffvelrnda
    @7
    @1
    @5
    wcel
    @9
    c2
    vy
    cv
    #
    chash
    cfv
    #
    cle
    wbr
    #
    @9
    vy
    @1
    @5
    @6
    @10
    @1
    wceq
    @11
    @8
    c2
    cle
    @10
    @1
    chash
    fveq2
    breq2d
    @4
    @12
    vx
    vy
    @5
    @2
    @10
    wceq
    @3
    @11
    c2
    cle
    @2
    @10
    chash
    fveq2
    breq2d
    cbvrabv
    elrab2
    simprbi
    syl
end
