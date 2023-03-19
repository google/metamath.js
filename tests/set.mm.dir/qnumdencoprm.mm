include "cq.mm"
include "wcel.mm"
include "cnumer.mm"
include "cfv.mm"
include "cdenom.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "cdiv.mm"
include "wa.mm"
include "eqidd.mm"
include "eqid.mm"
include "jctir.mm"
include "cz.mm"
include "cn.mm"
include "wb.mm"
include "qnumcl.mm"
include "qdencl.mm"
include "qnumdenbi.mm"
include "mpd3an23.mm"
include "mpbird.mm"
include "simpld.mm"

theorem qnumdencoprm
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A e. QQ -> ( ( numer ` A ) gcd ( denom ` A ) ) = 1 )

  proof
    cA
    cq
    wcel
    #
    cA
    cnumer
    cfv
    #
    cA
    cdenom
    cfv
    #
    cgcd
    co
    c1
    wceq
    #
    cA
    @1
    @2
    cdiv
    co
    wceq
    #
    @0
    @3
    @4
    wa
    #
    @1
    @1
    wceq
    #
    @2
    @2
    wceq
    #
    wa
    #
    @0
    @6
    @7
    @0
    @1
    eqidd
    @2
    eqid
    jctir
    @0
    @1
    cz
    wcel
    @2
    cn
    wcel
    @5
    @8
    wb
    cA
    qnumcl
    cA
    qdencl
    cA
    @1
    @2
    qnumdenbi
    mpd3an23
    mpbird
    simpld
end
