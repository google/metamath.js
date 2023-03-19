include "cr.mm"
include "wcel.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wa.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "cprime.mm"
include "cin.mm"
include "cfl.mm"
include "cfz.mm"
include "wceq.mm"
include "ppisval.mm"
include "adantr.mm"
include "wss.mm"
include "fzss1.mm"
include "adantl.mm"
include "ssrin.mm"
include "syl.mm"
include "cv.mm"
include "simpr.mm"
include "elin.mm"
include "sylib.mm"
include "simprd.mm"
include "prmuz2.mm"
include "simpld.mm"
include "elfzuz3.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"
include "elind.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "eqtrd.mm"

theorem ppisval2
  let cA: class A
  let cM: class M
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cK: class K
  let cN: class N
  let cS: class S
  let cB: class B
  let cP: class P


  assert |- ( ( A e. RR /\ 2 e. ( ZZ>= ` M ) ) -> ( ( 0 [,] A ) i^i Prime ) = ( ( M ... ( |_ ` A ) ) i^i Prime ) )

  proof
    cA
    cr
    wcel
    #
    c2
    cM
    cuz
    cfv
    wcel
    #
    wa
    #
    cc0
    cA
    cicc
    co
    cprime
    cin
    #
    c2
    cA
    cfl
    cfv
    #
    cfz
    co
    #
    cprime
    cin
    #
    cM
    @4
    cfz
    co
    #
    cprime
    cin
    #
    @0
    @3
    @6
    wceq
    @1
    cA
    ppisval
    adantr
    @2
    @6
    @8
    @2
    @5
    @7
    wss
    #
    @6
    @8
    wss
    @1
    @9
    @0
    c2
    cM
    @4
    fzss1
    adantl
    @5
    @7
    cprime
    ssrin
    syl
    @2
    vx
    @8
    @6
    @2
    vx
    cv
    #
    @8
    wcel
    #
    @10
    @6
    wcel
    @2
    @11
    wa
    #
    @5
    cprime
    @10
    @12
    @10
    c2
    cuz
    cfv
    wcel
    #
    @4
    @10
    cuz
    cfv
    wcel
    #
    @10
    @5
    wcel
    @12
    @10
    cprime
    wcel
    #
    @13
    @12
    @10
    @7
    wcel
    #
    @15
    @12
    @11
    @16
    @15
    wa
    @2
    @11
    simpr
    @10
    @7
    cprime
    elin
    sylib
    #
    simprd
    #
    @10
    prmuz2
    syl
    @12
    @16
    @14
    @12
    @16
    @15
    @17
    simpld
    @10
    cM
    @4
    elfzuz3
    syl
    @10
    c2
    @4
    elfzuzb
    sylanbrc
    @18
    elind
    ex
    ssrdv
    eqssd
    eqtrd
end
