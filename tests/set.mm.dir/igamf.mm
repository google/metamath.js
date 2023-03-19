include "cc.mm"
include "cv.mm"
include "cz.mm"
include "cn.mm"
include "cdif.mm"
include "wcel.mm"
include "cc0.mm"
include "c1.mm"
include "cgam.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "cif.mm"
include "cigam.mm"
include "df-igam.mm"
include "wa.mm"
include "0cnd.mm"
include "wn.mm"
include "eldif.mm"
include "gamcl.mm"
include "gamne0.mm"
include "reccld.mm"
include "sylbir.mm"
include "ifclda.mm"
include "fmpti.mm"

theorem igamf
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x
  let cA: class A


  assert |- 1/_G : CC --> CC

  proof
    vx
    cc
    cc
    vx
    cv
    #
    cz
    cn
    cdif
    #
    wcel
    #
    cc0
    c1
    @0
    cgam
    cfv
    #
    cdiv
    co
    #
    cif
    cigam
    vx
    df-igam
    @0
    cc
    wcel
    #
    @2
    cc0
    @4
    cc
    @5
    @2
    wa
    0cnd
    @5
    @2
    wn
    wa
    @0
    cc
    @1
    cdif
    wcel
    #
    @4
    cc
    wcel
    @0
    cc
    @1
    eldif
    @6
    @3
    @0
    gamcl
    @0
    gamne0
    reccld
    sylbir
    ifclda
    fmpti
end
