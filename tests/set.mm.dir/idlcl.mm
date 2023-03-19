include "crngo.mm"
include "wcel.mm"
include "cidl.mm"
include "cfv.mm"
include "wa.mm"
include "idlss.mm"
include "sselda.mm"

theorem idlcl
  let cA: class A
  let cR: class R
  let cG: class G
  let cI: class I
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume idlss.1: |- G = ( 1st ` R )
  assume idlss.2: |- X = ran G


  assert |- ( ( ( R e. RingOps /\ I e. ( Idl ` R ) ) /\ A e. I ) -> A e. X )

  proof
    cR
    crngo
    wcel
    cI
    cR
    cidl
    cfv
    wcel
    wa
    cI
    cX
    cA
    cR
    cG
    cI
    cX
    idlss.1
    idlss.2
    idlss
    sselda
end
