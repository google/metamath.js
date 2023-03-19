include "cn.mm"
include "wcel.mm"
include "cprime.mm"
include "cz.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cpc.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cexp.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "nnz.mm"
include "nnne0.mm"
include "jca.mm"
include "pczndvds.mm"
include "sylan2.mm"

theorem pcndvds
  let cP: class P
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vn: setvar n
  let vp: setvar p
  let vr: setvar r
  let vz: setvar z


  assert |- ( ( P e. Prime /\ N e. NN ) -> -. ( P ^ ( ( P pCnt N ) + 1 ) ) || N )

  proof
    cN
    cn
    wcel
    #
    cP
    cprime
    wcel
    cN
    cz
    wcel
    #
    cN
    cc0
    wne
    #
    wa
    cP
    cP
    cN
    cpc
    co
    c1
    caddc
    co
    cexp
    co
    cN
    cdvds
    wbr
    wn
    @0
    @1
    @2
    cN
    nnz
    cN
    nnne0
    jca
    cP
    cN
    pczndvds
    sylan2
end
