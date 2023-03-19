include "wcel.mm"
include "wa.mm"
include "wf1.mm"
include "wfo.mm"
include "wf1o.mm"
include "symgextf1.mm"
include "symgextfo.mm"
include "df-f1o.mm"
include "sylanbrc.mm"

theorem symgextf1o
  let vx: setvar x
  let cS: class S
  let cE: class E
  let cK: class K
  let cN: class N
  let cZ: class Z
  let cX: class X
  let cY: class Y
  let vy: setvar y
  let vz: setvar z
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  assume symgext.s: |- S = ( Base ` ( SymGrp ` ( N \ { K } ) ) )
  assume symgext.e: |- E = ( x e. N |-> if ( x = K , K , ( Z ` x ) ) )

  disjoint K x
  disjoint N x
  disjoint S x
  disjoint Z x
  disjoint X x
  disjoint Y x
  disjoint E y
  disjoint E z
  disjoint y z
  disjoint K i
  disjoint K j
  disjoint K y
  disjoint i j
  disjoint i y
  disjoint j y
  disjoint K z
  disjoint N i
  disjoint N j
  disjoint N y
  disjoint N z
  disjoint S y
  disjoint S z
  disjoint Z i
  disjoint Z j
  disjoint Z y
  disjoint Z z
  disjoint x y
  disjoint x z
  disjoint j z
  disjoint E i
  disjoint E k
  disjoint i k
  disjoint K k
  disjoint N k
  disjoint S i
  disjoint S k
  disjoint Z k
  disjoint i x
  assert |- ( ( K e. N /\ Z e. S ) -> E : N -1-1-onto-> N )

  proof
    cK
    cN
    wcel
    cZ
    cS
    wcel
    wa
    cN
    cN
    cE
    wf1
    cN
    cN
    cE
    wfo
    cN
    cN
    cE
    wf1o
    vx
    cS
    cE
    cK
    cN
    cZ
    symgext.s
    symgext.e
    symgextf1
    vx
    cS
    cE
    cK
    cN
    cZ
    symgext.s
    symgext.e
    symgextfo
    cN
    cN
    cE
    df-f1o
    sylanbrc
end
