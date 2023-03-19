include "wcel.mm"
include "wbr.mm"
include "isat.mm"
include "baibd.mm"

theorem isat2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cK: class K
  let c.0: class .0.
  let vx: setvar x
  assume isatom.b: |- B = ( Base ` K )
  assume isatom.z: |- .0. = ( 0. ` K )
  assume isatom.c: |- C = ( <o ` K )
  assume isatom.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. D /\ P e. B ) -> ( P e. A <-> .0. C P ) )

  proof
    cK
    cD
    wcel
    cP
    cA
    wcel
    cP
    cB
    wcel
    c.0
    cP
    cC
    wbr
    cA
    cB
    cC
    cD
    cP
    cK
    c.0
    isatom.b
    isatom.z
    isatom.c
    isatom.a
    isat
    baibd
end
