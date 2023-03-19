include "clmod.mm"
include "wcel.mm"
include "csca.mm"
include "cfv.mm"
include "cbs.mm"
include "chash.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "wo.mm"
include "cnzr.mm"
include "wn.mm"
include "cpw.mm"
include "clininds.mm"
include "wbr.mm"
include "w3a.mm"
include "simp2.mm"
include "crg.mm"
include "wb.mm"
include "eqid.mm"
include "lmodring.mm"
include "3ad2ant1.mm"
include "0ringnnzr.mm"
include "syl.mm"
include "mpbird.mm"
include "olcd.mm"
include "lindsrng01.mm"
include "syld3an2.mm"

theorem lindszr
  let cS: class S
  let cM: class M
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( M e. LMod /\ -. ( Scalar ` M ) e. NzRing /\ S e. ~P ( Base ` M ) ) -> S linIndS M )

  proof
    cM
    clmod
    wcel
    #
    cM
    csca
    cfv
    #
    cbs
    cfv
    #
    chash
    cfv
    #
    cc0
    wceq
    #
    @3
    c1
    wceq
    #
    wo
    @1
    cnzr
    wcel
    wn
    #
    cS
    cM
    cbs
    cfv
    #
    cpw
    wcel
    #
    cS
    cM
    clininds
    wbr
    @0
    @6
    @8
    w3a
    #
    @5
    @4
    @9
    @5
    @6
    @0
    @6
    @8
    simp2
    @9
    @1
    crg
    wcel
    #
    @5
    @6
    wb
    @0
    @6
    @10
    @8
    @1
    cM
    @1
    eqid
    #
    lmodring
    3ad2ant1
    @1
    0ringnnzr
    syl
    mpbird
    olcd
    @7
    @1
    cS
    @2
    cM
    @7
    eqid
    @11
    @2
    eqid
    lindsrng01
    syld3an2
end
