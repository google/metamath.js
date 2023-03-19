include "cdvds.mm"
include "wbr.mm"
include "cop.mm"
include "cv.mm"
include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "copab.mm"
include "df-br.mm"
include "df-dvds.mm"
include "eleq2i.mm"
include "bitri.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "eqeq2.mm"
include "opelopab2.mm"
include "syl5bb.mm"

theorem divides
  let vn: setvar n
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vy: setvar y

  disjoint M n
  disjoint N n
  disjoint M x
  disjoint M y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint N x
  disjoint N y
  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M || N <-> E. n e. ZZ ( n x. M ) = N ) )

  proof
    cM
    cN
    cdvds
    wbr
    #
    cM
    cN
    cop
    #
    vx
    cv
    #
    cz
    wcel
    vy
    cv
    #
    cz
    wcel
    wa
    vn
    cv
    #
    @2
    cmul
    co
    #
    @3
    wceq
    #
    vn
    cz
    wrex
    #
    wa
    vx
    vy
    copab
    #
    wcel
    #
    cM
    cz
    wcel
    cN
    cz
    wcel
    wa
    @4
    cM
    cmul
    co
    #
    cN
    wceq
    #
    vn
    cz
    wrex
    #
    @0
    @1
    cdvds
    wcel
    @9
    cM
    cN
    cdvds
    df-br
    cdvds
    @8
    @1
    vx
    vy
    vn
    df-dvds
    eleq2i
    bitri
    @7
    @10
    @3
    wceq
    #
    vn
    cz
    wrex
    @12
    vx
    vy
    cM
    cN
    cz
    cz
    @2
    cM
    wceq
    #
    @6
    @13
    vn
    cz
    @14
    @5
    @10
    @3
    @2
    cM
    @4
    cmul
    oveq2
    eqeq1d
    rexbidv
    @3
    cN
    wceq
    @13
    @11
    vn
    cz
    @3
    cN
    @10
    eqeq2
    rexbidv
    opelopab2
    syl5bb
end
