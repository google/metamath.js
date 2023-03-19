include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "clgs.mm"
include "co.mm"
include "wceq.mm"
include "c2.mm"
include "cexp.mm"
include "c1.mm"
include "cif.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cneg.mm"
include "cabs.mm"
include "cfv.mm"
include "cmul.mm"
include "cn.mm"
include "cv.mm"
include "cprime.mm"
include "cdvds.mm"
include "c8.mm"
include "cmo.mm"
include "c7.mm"
include "cpr.mm"
include "cmin.mm"
include "cdiv.mm"
include "caddc.mm"
include "cpc.mm"
include "cmpt.mm"
include "cseq.mm"
include "0z.mm"
include "eqid.mm"
include "lgsval.mm"
include "mpan2.mm"
include "iftruei.mm"
include "syl6eq.mm"

theorem lgs0
  let cA: class A
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cN: class N
  let cP: class P


  assert |- ( A e. ZZ -> ( A /L 0 ) = if ( ( A ^ 2 ) = 1 , 1 , 0 ) )

  proof
    cA
    cz
    wcel
    #
    cA
    cc0
    clgs
    co
    #
    cc0
    cc0
    wceq
    #
    cA
    c2
    cexp
    co
    c1
    wceq
    c1
    cc0
    cif
    #
    cc0
    cc0
    clt
    wbr
    cA
    cc0
    clt
    wbr
    wa
    c1
    cneg
    #
    c1
    cif
    cc0
    cabs
    cfv
    cmul
    vn
    cn
    vn
    cv
    #
    cprime
    wcel
    @5
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
    @4
    cif
    cif
    cA
    @5
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
    @5
    cmo
    co
    c1
    cmin
    co
    cif
    @5
    cc0
    cpc
    co
    cexp
    co
    c1
    cif
    cmpt
    #
    c1
    cseq
    cfv
    cmul
    co
    #
    cif
    #
    @3
    @0
    cc0
    cz
    wcel
    @1
    @8
    wceq
    0z
    cA
    vn
    @6
    cc0
    @6
    eqid
    lgsval
    mpan2
    @2
    @3
    @7
    cc0
    eqid
    iftruei
    syl6eq
end
