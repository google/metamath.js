include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "clgs.mm"
include "co.mm"
include "wceq.mm"
include "cdvds.mm"
include "wbr.mm"
include "cc0.mm"
include "c8.mm"
include "cmo.mm"
include "c1.mm"
include "c7.mm"
include "cpr.mm"
include "cneg.mm"
include "cif.mm"
include "cmin.mm"
include "cdiv.mm"
include "cexp.mm"
include "caddc.mm"
include "cprime.mm"
include "2prm.mm"
include "lgsval2.mm"
include "mpan2.mm"
include "eqid.mm"
include "iftruei.mm"
include "syl6eq.mm"

theorem lgs2
  let cA: class A
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cN: class N
  let cP: class P


  assert |- ( A e. ZZ -> ( A /L 2 ) = if ( 2 || A , 0 , if ( ( A mod 8 ) e. { 1 , 7 } , 1 , -u 1 ) ) )

  proof
    cA
    cz
    wcel
    #
    cA
    c2
    clgs
    co
    #
    c2
    c2
    wceq
    #
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
    #
    cA
    c2
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
    c2
    cmo
    co
    c1
    cmin
    co
    #
    cif
    #
    @3
    @0
    c2
    cprime
    wcel
    @1
    @5
    wceq
    2prm
    cA
    c2
    lgsval2
    mpan2
    @2
    @3
    @4
    c2
    eqid
    iftruei
    syl6eq
end
