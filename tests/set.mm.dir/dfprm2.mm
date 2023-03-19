include "cprime.mm"
include "cn.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "prmnn.mm"
include "prmirredlem.mm"
include "bicomd.mm"
include "biadan2.mm"
include "elin.mm"
include "bitr4i.mm"
include "eqriv.mm"

theorem dfprm2
  let cI: class I
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  assume prmirred.i: |- I = ( Irred ` ZZring )


  assert |- Prime = ( NN i^i I )

  proof
    vx
    cprime
    cn
    cI
    cin
    #
    vx
    cv
    #
    cprime
    wcel
    #
    @1
    cn
    wcel
    #
    @1
    cI
    wcel
    #
    wa
    @1
    @0
    wcel
    @2
    @3
    @4
    @1
    prmnn
    @3
    @4
    @2
    @1
    cI
    prmirred.i
    prmirredlem
    bicomd
    biadan2
    @1
    cn
    cI
    elin
    bitr4i
    eqriv
end
