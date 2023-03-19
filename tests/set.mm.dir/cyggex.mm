include "ccyg.mm"
include "wcel.mm"
include "cfn.mm"
include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "cif.mm"
include "cyggex2.mm"
include "iftrue.mm"
include "sylan9eq.mm"

theorem cyggex
  let cB: class B
  let cE: class E
  let cG: class G
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let cH: class H
  assume cygctb.1: |- B = ( Base ` G )
  assume cyggex.o: |- E = ( gEx ` G )


  assert |- ( ( G e. CycGrp /\ B e. Fin ) -> E = ( # ` B ) )

  proof
    cG
    ccyg
    wcel
    cB
    cfn
    wcel
    #
    cE
    @0
    cB
    chash
    cfv
    #
    cc0
    cif
    @1
    cB
    cE
    cG
    cygctb.1
    cyggex.o
    cyggex2
    @0
    @1
    cc0
    iftrue
    sylan9eq
end
