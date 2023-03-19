include "wcel.mm"
include "w3a.mm"
include "csymg.mm"
include "cfv.mm"
include "cbs.mm"
include "wf1o.mm"
include "symgextf1o.mm"
include "3adant1.mm"
include "wb.mm"
include "eqid.mm"
include "elsymgbas.mm"
include "3ad2ant1.mm"
include "mpbird.mm"

theorem symgextsymg
  let vx: setvar x
  let cS: class S
  let cE: class E
  let cK: class K
  let cN: class N
  let cV: class V
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
  assert |- ( ( N e. V /\ K e. N /\ Z e. S ) -> E e. ( Base ` ( SymGrp ` N ) ) )

  proof
    cN
    cV
    wcel
    #
    cK
    cN
    wcel
    #
    cZ
    cS
    wcel
    #
    w3a
    cE
    cN
    csymg
    cfv
    #
    cbs
    cfv
    #
    wcel
    #
    cN
    cN
    cE
    wf1o
    #
    @1
    @2
    @6
    @0
    vx
    cS
    cE
    cK
    cN
    cZ
    symgext.s
    symgext.e
    symgextf1o
    3adant1
    @0
    @1
    @5
    @6
    wb
    @2
    cN
    @4
    cE
    @3
    cV
    @3
    eqid
    @4
    eqid
    elsymgbas
    3ad2ant1
    mpbird
end
