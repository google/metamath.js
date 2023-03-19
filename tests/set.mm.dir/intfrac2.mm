include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "clt.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cfl.mm"
include "cfv.mm"
include "cmin.mm"
include "fracge0.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "syl6breqr.mm"
include "fraclt1.mm"
include "syl5eqbr.mm"
include "cz.mm"
include "flcl.mm"
include "syl5eqel.mm"
include "zcnd.mm"
include "recn.mm"
include "pncan3d.mm"
include "syl5req.mm"
include "3jca.mm"

theorem intfrac2
  let cA: class A
  let cF: class F
  let cZ: class Z
  assume intfrac2.1: |- Z = ( |_ ` A )
  assume intfrac2.2: |- F = ( A - Z )


  assert |- ( A e. RR -> ( 0 <_ F /\ F < 1 /\ A = ( Z + F ) ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cF
    cle
    wbr
    cF
    c1
    clt
    wbr
    cA
    cZ
    cF
    caddc
    co
    #
    wceq
    @0
    cc0
    cA
    cA
    cfl
    cfv
    #
    cmin
    co
    #
    cF
    cle
    cA
    fracge0
    cF
    cA
    cZ
    cmin
    co
    #
    @3
    intfrac2.2
    cZ
    @2
    cA
    cmin
    intfrac2.1
    oveq2i
    eqtri
    #
    syl6breqr
    @0
    cF
    @3
    c1
    clt
    @5
    cA
    fraclt1
    syl5eqbr
    @0
    @1
    cZ
    @4
    caddc
    co
    cA
    cF
    @4
    cZ
    caddc
    intfrac2.2
    oveq2i
    @0
    cZ
    cA
    @0
    cZ
    @0
    cZ
    @2
    cz
    intfrac2.1
    cA
    flcl
    syl5eqel
    zcnd
    cA
    recn
    pncan3d
    syl5req
    3jca
end
