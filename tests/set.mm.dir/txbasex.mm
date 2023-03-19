include "wcel.mm"
include "wa.mm"
include "cuni.mm"
include "cvv.mm"
include "cxp.mm"
include "eqid.mm"
include "txuni2.mm"
include "uniexg.mm"
include "xpexg.mm"
include "syl2an.mm"
include "syl5eqelr.mm"
include "uniexb.mm"
include "sylibr.mm"

theorem txbasex
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let cS: class S
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vp: setvar p
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  let vw: setvar w
  let cX: class X
  let cY: class Y
  assume txval.1: |- B = ran ( x e. R , y e. S |-> ( x X. y ) )

  disjoint x y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a p
  disjoint a r
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint R a
  disjoint b c
  disjoint b d
  disjoint b p
  disjoint b r
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint R b
  disjoint c d
  disjoint c p
  disjoint c r
  disjoint c s
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint R c
  disjoint d p
  disjoint d r
  disjoint d s
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint R d
  disjoint p r
  disjoint p s
  disjoint p t
  disjoint p u
  disjoint p v
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint R p
  disjoint r s
  disjoint r t
  disjoint r u
  disjoint r v
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint R r
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint R s
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint R t
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint R u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint R v
  disjoint x z
  disjoint y z
  disjoint R z
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint S p
  disjoint S r
  disjoint S s
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S z
  disjoint a w
  disjoint B a
  disjoint b w
  disjoint B b
  disjoint c w
  disjoint B c
  disjoint d w
  disjoint B d
  disjoint p w
  disjoint B p
  disjoint r w
  disjoint B r
  disjoint s w
  disjoint B s
  disjoint t w
  disjoint B t
  disjoint u w
  disjoint B u
  disjoint v w
  disjoint B v
  disjoint w z
  disjoint B w
  disjoint B z
  disjoint w x
  disjoint w y
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  assert |- ( ( R e. V /\ S e. W ) -> B e. _V )

  proof
    cR
    cV
    wcel
    #
    cS
    cW
    wcel
    #
    wa
    #
    cB
    cuni
    #
    cvv
    wcel
    cB
    cvv
    wcel
    @2
    @3
    cR
    cuni
    #
    cS
    cuni
    #
    cxp
    #
    cvv
    vx
    vy
    cB
    cR
    cS
    @4
    @5
    txval.1
    @4
    eqid
    @5
    eqid
    txuni2
    @0
    @4
    cvv
    wcel
    @5
    cvv
    wcel
    @6
    cvv
    wcel
    @1
    cR
    cV
    uniexg
    cS
    cW
    uniexg
    @4
    @5
    cvv
    cvv
    xpexg
    syl2an
    syl5eqelr
    cB
    uniexb
    sylibr
end
