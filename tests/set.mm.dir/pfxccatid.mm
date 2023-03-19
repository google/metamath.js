include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cconcat.mm"
include "co.mm"
include "cpfx.mm"
include "cc0.mm"
include "cfz.mm"
include "cn0.mm"
include "lencl.mm"
include "nn0fz0.mm"
include "sylib.mm"
include "3ad2ant1.mm"
include "wb.mm"
include "eleq1.mm"
include "3ad2ant3.mm"
include "mpbird.mm"
include "eqid.mm"
include "pfxccatpfx1.mm"
include "syld3an3.mm"
include "oveq2.mm"
include "pfxid.mm"
include "3eqtrd.mm"

theorem pfxccatid
  let cA: class A
  let cB: class B
  let cN: class N
  let cV: class V
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. Word V /\ B e. Word V /\ N = ( # ` A ) ) -> ( ( A ++ B ) prefix N ) = A )

  proof
    cA
    cV
    cword
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cN
    cA
    chash
    cfv
    #
    wceq
    #
    w3a
    #
    cA
    cB
    cconcat
    co
    cN
    cpfx
    co
    #
    cA
    cN
    cpfx
    co
    #
    cA
    @3
    cpfx
    co
    #
    cA
    @1
    @2
    @4
    cN
    cc0
    @3
    cfz
    co
    #
    wcel
    #
    @6
    @7
    wceq
    @5
    @10
    @3
    @9
    wcel
    #
    @1
    @2
    @11
    @4
    @1
    @3
    cn0
    wcel
    @11
    cV
    cA
    lencl
    @3
    nn0fz0
    sylib
    3ad2ant1
    @4
    @1
    @10
    @11
    wb
    @2
    cN
    @3
    @9
    eleq1
    3ad2ant3
    mpbird
    cA
    cB
    @3
    cN
    cV
    @3
    eqid
    pfxccatpfx1
    syld3an3
    @4
    @1
    @7
    @8
    wceq
    @2
    cN
    @3
    cA
    cpfx
    oveq2
    3ad2ant3
    @1
    @2
    @8
    cA
    wceq
    @4
    cV
    cA
    pfxid
    3ad2ant1
    3eqtrd
end
