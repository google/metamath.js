include "cn.mm"
include "cv.mm"
include "cprime.mm"
include "wcel.mm"
include "c2.mm"
include "wceq.mm"
include "cdvds.mm"
include "wbr.mm"
include "cc0.mm"
include "c8.mm"
include "cmo.mm"
include "co.mm"
include "c1.mm"
include "c7.mm"
include "cpr.mm"
include "cneg.mm"
include "cif.mm"
include "cmin.mm"
include "cdiv.mm"
include "cexp.mm"
include "caddc.mm"
include "cpc.mm"
include "cmpt.mm"
include "eqid.mm"
include "lgsval2lem.mm"

theorem lgsval2
  let cA: class A
  let cP: class P
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cN: class N


  assert |- ( ( A e. ZZ /\ P e. Prime ) -> ( A /L P ) = if ( P = 2 , if ( 2 || A , 0 , if ( ( A mod 8 ) e. { 1 , 7 } , 1 , -u 1 ) ) , ( ( ( ( A ^ ( ( P - 1 ) / 2 ) ) + 1 ) mod P ) - 1 ) ) )

  proof
    cA
    vn
    vn
    cn
    vn
    cv
    #
    cprime
    wcel
    @0
    c2
    wceq
    c2
    cA
    cdvds
    wbr
    cc0
    cA
    c8
    cmo
    co
    c1
    c7
    cpr
    wcel
    c1
    c1
    cneg
    cif
    cif
    cA
    @0
    c1
    cmin
    co
    c2
    cdiv
    co
    cexp
    co
    c1
    caddc
    co
    @0
    cmo
    co
    c1
    cmin
    co
    cif
    @0
    cP
    cpc
    co
    cexp
    co
    c1
    cif
    cmpt
    #
    cP
    @1
    eqid
    lgsval2lem
end
