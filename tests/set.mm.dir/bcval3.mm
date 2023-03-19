include "cn0.mm"
include "wcel.mm"
include "cz.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wn.mm"
include "w3a.mm"
include "cbc.mm"
include "cfa.mm"
include "cfv.mm"
include "cmin.mm"
include "cmul.mm"
include "cdiv.mm"
include "cif.mm"
include "wceq.mm"
include "bcval.mm"
include "3adant3.mm"
include "iffalse.mm"
include "3ad2ant3.mm"
include "eqtrd.mm"

theorem bcval3
  let cK: class K
  let cN: class N
  let vk: setvar k
  let vn: setvar n


  assert |- ( ( N e. NN0 /\ K e. ZZ /\ -. K e. ( 0 ... N ) ) -> ( N _C K ) = 0 )

  proof
    cN
    cn0
    wcel
    #
    cK
    cz
    wcel
    #
    cK
    cc0
    cN
    cfz
    co
    wcel
    #
    wn
    #
    w3a
    cN
    cK
    cbc
    co
    #
    @2
    cN
    cfa
    cfv
    cN
    cK
    cmin
    co
    cfa
    cfv
    cK
    cfa
    cfv
    cmul
    co
    cdiv
    co
    #
    cc0
    cif
    #
    cc0
    @0
    @1
    @4
    @6
    wceq
    @3
    cK
    cN
    bcval
    3adant3
    @3
    @0
    @6
    cc0
    wceq
    @1
    @2
    @5
    cc0
    iffalse
    3ad2ant3
    eqtrd
end
