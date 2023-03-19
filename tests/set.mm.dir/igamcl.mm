include "cc.mm"
include "wcel.mm"
include "cigam.mm"
include "cfv.mm"
include "cz.mm"
include "cn.mm"
include "cdif.mm"
include "cc0.mm"
include "c1.mm"
include "cgam.mm"
include "cdiv.mm"
include "co.mm"
include "cif.mm"
include "igamval.mm"
include "wa.mm"
include "0cnd.mm"
include "wn.mm"
include "eldif.mm"
include "gamcl.mm"
include "gamne0.mm"
include "reccld.mm"
include "sylbir.mm"
include "ifclda.mm"
include "eqeltrd.mm"

theorem igamcl
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x


  assert |- ( A e. CC -> ( 1/_G ` A ) e. CC )

  proof
    cA
    cc
    wcel
    #
    cA
    cigam
    cfv
    cA
    cz
    cn
    cdif
    #
    wcel
    #
    cc0
    c1
    cA
    cgam
    cfv
    #
    cdiv
    co
    #
    cif
    cc
    cA
    igamval
    @0
    @2
    cc0
    @4
    cc
    @0
    @2
    wa
    0cnd
    @0
    @2
    wn
    wa
    cA
    cc
    @1
    cdif
    wcel
    #
    @4
    cc
    wcel
    cA
    cc
    @1
    eldif
    @5
    @3
    cA
    gamcl
    cA
    gamne0
    reccld
    sylbir
    ifclda
    eqeltrd
end
