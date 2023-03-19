include "c0.mm"
include "cfv.mm"
include "coa.mm"
include "co.mm"
include "wceq.mm"
include "cun.mm"
include "com.mm"
include "wcel.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "ackbij1lem10.mm"
include "peano1.mm"
include "f0cli.mm"
include "nna0.mm"
include "ax-mp.mm"
include "un0.mm"
include "fveq2i.mm"
include "ackbij1lem3.mm"
include "in0.mm"
include "ackbij1lem9.mm"
include "mp3an.mm"
include "3eqtr2ri.mm"
include "wb.mm"
include "nnacan.mm"
include "mpbi.mm"

theorem ackbij1lem13
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cG: class G
  let cH: class H
  let cA: class A
  let cB: class B
  assume ackbij.f: |- F = ( x e. ( ~P _om i^i Fin ) |-> ( card ` U_ y e. x ( { y } X. ~P y ) ) )

  disjoint F x
  disjoint F y
  disjoint x y
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
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
  disjoint A c
  disjoint A x
  disjoint A y
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B x
  disjoint B y
  assert |- ( F ` (/) ) = (/)

  proof
    c0
    cF
    cfv
    #
    @0
    coa
    co
    #
    @0
    c0
    coa
    co
    #
    wceq
    #
    @0
    c0
    wceq
    #
    @2
    @0
    c0
    c0
    cun
    #
    cF
    cfv
    #
    @1
    @0
    com
    wcel
    #
    @2
    @0
    wceq
    com
    cpw
    cfn
    cin
    #
    com
    c0
    cF
    vx
    vy
    cF
    ackbij.f
    ackbij1lem10
    peano1
    f0cli
    #
    @0
    nna0
    ax-mp
    @5
    c0
    cF
    c0
    un0
    fveq2i
    c0
    @8
    wcel
    #
    @10
    c0
    c0
    cin
    c0
    wceq
    @6
    @1
    wceq
    c0
    com
    wcel
    #
    @10
    peano1
    c0
    ackbij1lem3
    ax-mp
    #
    @12
    c0
    in0
    vx
    vy
    c0
    c0
    cF
    ackbij.f
    ackbij1lem9
    mp3an
    3eqtr2ri
    @7
    @7
    @11
    @3
    @4
    wb
    @9
    @9
    peano1
    @0
    @0
    c0
    nnacan
    mp3an
    mpbi
end
