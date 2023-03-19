include "c0.mm"
include "cv.mm"
include "wcel.mm"
include "cdif.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wdisj.mm"
include "wa.mm"
include "cuni.mm"
include "wi.mm"
include "cpw.mm"
include "w3a.mm"
include "wceq.mm"
include "eleq2.mm"
include "raleqbi1dv.mm"
include "pweq.mm"
include "imbi2d.mm"
include "raleqbidv.mm"
include "3anbi123d.mm"
include "elrab2.mm"

theorem isldsys
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cL: class L
  let cO: class O
  let vs: setvar s
  let vu: setvar u
  let vt: setvar t
  let cV: class V
  assume isldsys.l: |- L = { s e. ~P ~P O | ( (/) e. s /\ A. x e. s ( O \ x ) e. s /\ A. x e. ~P s ( ( x ~<_ _om /\ Disj_ y e. x y ) -> U. x e. s ) ) }

  disjoint s y
  disjoint O s
  disjoint O x
  disjoint s x
  disjoint S s
  disjoint S x
  disjoint s u
  disjoint u y
  disjoint L t
  disjoint O t
  disjoint s t
  disjoint t x
  disjoint V x
  assert |- ( S e. L <-> ( S e. ~P ~P O /\ ( (/) e. S /\ A. x e. S ( O \ x ) e. S /\ A. x e. ~P S ( ( x ~<_ _om /\ Disj_ y e. x y ) -> U. x e. S ) ) ) )

  proof
    c0
    vs
    cv
    #
    wcel
    #
    cO
    vx
    cv
    #
    cdif
    #
    @0
    wcel
    #
    vx
    @0
    wral
    #
    @2
    com
    cdom
    wbr
    vy
    @2
    vy
    cv
    wdisj
    wa
    #
    @2
    cuni
    #
    @0
    wcel
    #
    wi
    #
    vx
    @0
    cpw
    #
    wral
    #
    w3a
    c0
    cS
    wcel
    #
    @3
    cS
    wcel
    #
    vx
    cS
    wral
    #
    @6
    @7
    cS
    wcel
    #
    wi
    #
    vx
    cS
    cpw
    #
    wral
    #
    w3a
    vs
    cS
    cO
    cpw
    cpw
    cL
    @0
    cS
    wceq
    #
    @1
    @12
    @5
    @14
    @11
    @18
    @0
    cS
    c0
    eleq2
    @4
    @13
    vx
    @0
    cS
    @0
    cS
    @3
    eleq2
    raleqbi1dv
    @19
    @9
    @16
    vx
    @10
    @17
    @0
    cS
    pweq
    @19
    @8
    @15
    @6
    @0
    cS
    @7
    eleq2
    imbi2d
    raleqbidv
    3anbi123d
    isldsys.l
    elrab2
end
